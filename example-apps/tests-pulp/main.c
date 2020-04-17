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

#include <assert.h>
#include <stdio.h>
#include <stdlib.h> // abort()
#include "tests.h"

void __assert_func(const char* file, int line, const char* funcname, const char* assertion) {
  printf("Assertion `%s' in %s (%s:%d) failed!\n", assertion, funcname, file, line);
  abort();
}

unsigned report_pass_fail(int (*fn)(), const char* name)
{
  printf("Testing %s ..\n", name);
  if (fn()) {
    return 0;
  } else {
    printf("%s failed!\n", name);
    return 1;
  }
}

unsigned report_n_errors(unsigned (*fn)(), const char* name)
{
  printf("Testing %s ..\n", name);
  const unsigned n_errors = fn();
  if (n_errors == 0) {
    return 0;
  } else {
    printf("%s failed with %d errors!\n", name, n_errors);
    return n_errors;
  }
}

int main(int argc, char *argv[])
{
  unsigned n_errors = 0;

  n_errors += report_n_errors(test_m_instrs, "M instructions");
  n_errors += report_n_errors(test_dma, "DMA transfers");
  n_errors += report_n_errors(test_floats, "floating-point calculations");
  n_errors += report_n_errors(test_atomic, "atomic memory accesses");
  n_errors += report_n_errors(test_intrinsics, "PULP intrinsics");
  n_errors += report_n_errors(test_memory, "various memory ranges");

  n_errors += report_pass_fail(
      gcc_omp_parallel_for_schedule_static,
      "GCC `omp parallel for` with static schedule with pointers");

  assert(n_errors == 0);
  return n_errors;
}
