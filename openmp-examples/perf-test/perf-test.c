/*
 * HERO Performance API Test Application
 *
 * Copyright 2021 ETH Zurich, University of Bologna
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <hero-target.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

int measure_event(const hero_perf_event_t event) {
  int counter;
#pragma omp target device(BIGPULP_MEMCPY) map(to : event) map(from : counter)
  {
    volatile uint32_t* const l1_ptr = (__device volatile uint32_t*)hero_l1malloc(sizeof(uint32_t));
    if (l1_ptr == NULL) {
      printf("Error allocating L1 memory!\n");
      goto __end;
    }

    const int alloc = hero_perf_alloc(event);
    if (alloc != 0) {
      printf("Error allocating performance counter: %d!\n", alloc);
      goto __free;
    }

    hero_perf_continue_all();
    // 3 local loads
    const uint32_t l1_var = *l1_ptr;
    const uint32_t l1_var_1 = *l1_ptr;
    const uint32_t l1_var_2 = *l1_ptr;
    // 1 local stores
    *l1_ptr = 42;
    hero_perf_pause_all();

    // 1 local load and 1 local store, which must not be counted.
    *l1_ptr = 178;
    const uint32_t l1_var_3 = *l1_ptr;

    counter = hero_perf_read(event);

    const int dealloc = hero_perf_dealloc(event);
    if (dealloc != 0) {
      printf("Error deallocating performance counter: %d!\n", dealloc);
    }
  __free:
    hero_l1free(l1_ptr);
  __end : {}
  }
  return counter;
}

int measure_compare(const hero_perf_event_t event, const char* suffix, const unsigned expected) {
  const int actual = measure_event(event);
  if (actual != expected) {
    printf("Error for hero_perf_event_%s: expected %d, measured %d!\n", suffix, expected, actual);
    return 1;
  }
  return 0;
}

int main(int argc, char* argv[]) {

  int init;
#pragma omp target device(BIGPULP_MEMCPY) map(from : init)
  { init = hero_perf_init(); }
  if (init != 0) {
    printf("Error initializing performance measurement: %d!\n", init);
    abort();
  }

  unsigned n_errors = 0;
  n_errors += measure_compare(hero_perf_event_load, "load", 3);
  n_errors += measure_compare(hero_perf_event_store, "store", 1);
  n_errors += measure_compare(hero_perf_event_load_external, "load_external", 0);
  n_errors += measure_compare(hero_perf_event_store_external, "store_external", 0);

#pragma omp target device(BIGPULP_MEMCPY)
  { hero_perf_term(); }

  if (n_errors == 0) {
    printf("Test successful.\n");
    return 0;
  } else {
    return 1;
  }
}
