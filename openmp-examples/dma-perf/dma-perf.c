/*
 * HERO DMA Performance Benchmark
 *
 * Copyright 2020 ETH Zurich, University of Bologna
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
#include <omp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#define BUF_L3 (void*) 0x80000000

void perform_benchmark(const unsigned buf_size_kib) {
  unsigned cyc_31, cyc_13;
  const unsigned buf_size_bytes = buf_size_kib * 1024;

#pragma omp target device(BIGPULP_MEMCPY) map(to : buf_size_bytes) map(from : cyc_13, cyc_31)
  {
    __device uint32_t* const buf_l1 = (__device uint32_t*)hero_l1malloc(buf_size_bytes);
    if (buf_l1 == NULL) {
      printf("ERROR: hero_l1malloc() failed\n");
      abort();
    }

    // L1 to L3 (RAM) with DMA
    hero_reset_clk_counter();
    hero_memcpy_host2dev(buf_l1, (__host void*)BUF_L3, buf_size_bytes);
    cyc_31 = hero_get_clk_counter();

    // L3 (RAM) to L1 with DMA
    hero_reset_clk_counter();
    hero_memcpy_dev2host((__host void*)BUF_L3, buf_l1, buf_size_bytes);
    cyc_13 = hero_get_clk_counter();

    hero_l1free(buf_l1);
  }

  const double perf_31 = ((double)buf_size_bytes) / cyc_31;
  const double perf_13 = ((double)buf_size_bytes) / cyc_13;
  printf("For transfer size %d KiB:\n", buf_size_kib);
  printf("L3 -> L1 DMA: %.3f bytes/cycle\n", perf_31);
  printf("L1 -> L3 DMA: %.3f bytes/cycle\n", perf_13);
}

int main(int argc, char* argv[]) {
  omp_set_default_device(BIGPULP_SVM);

  unsigned buf_size_kib[] = {1, 2, 4, 8, 16, 32, 64, 96, 110};
  for (unsigned i = 0; i < sizeof(buf_size_kib) / sizeof(unsigned); i++) {
    perform_benchmark(buf_size_kib[i]);
  }

  return 0;
}


