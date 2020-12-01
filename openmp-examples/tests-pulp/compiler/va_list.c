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
#include "hero-target.h"

uint32_t read_n_vaargs(uint32_t n, ...) {
  uint32_t n_errors = 0;
  va_list vaargs;
  va_start(vaargs, n);
  for (int i = 0; i < n; i++) {
    uint32_t arg = va_arg(vaargs, uint32_t);
    if (arg != i) {
      n_errors++;
    }
  }
  va_end(vaargs);
  return n_errors;
}

unsigned test_va_list()
{
  unsigned n_errors = 0;

  printf("Read 1 argument.\n");
  n_errors += read_n_vaargs(1, 0);
  printf("Read 2 argument.\n");
  n_errors += read_n_vaargs(2, 0, 1);
  printf("Read 3 argument.\n");
  n_errors += read_n_vaargs(3, 0, 1, 2);
  printf("Read 4 argument.\n");
  n_errors += read_n_vaargs(4, 0, 1, 2, 3);

  return n_errors;
}
