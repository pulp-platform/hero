/*
 * Copyright 2019 ETH Zurich, University of Bologna
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

#include <stdint.h>
#include <string.h> // memset()
#include "hero-target.h"

#define SIZE 64
#define ITER 4

unsigned check_bytes(char *arr, char val, int len) {
  unsigned n_errors = 0;
  for (int i = 0; i < len; i++) {
    if (arr[i] != val) {
      n_errors++;
    }
  }
  return n_errors;
}

// Issue #25 claims that memset doesn't do anything. Here we test that.
unsigned test_memset()
{
  unsigned n_errors = 0;
  uint32_t *arr = (__device uint32_t *) hero_l1malloc(SIZE * sizeof(uint32_t));
  for (char c = 0; c < ITER; c++) {
    printf("Memset pass %d\n", (int)c);
    memset(arr, c, SIZE * sizeof(uint32_t));
    n_errors = check_bytes((__device char *)arr, c, SIZE * sizeof(uint32_t));
  }
  printf("Memset finished with %u errors\n", n_errors);

  return n_errors;
}
