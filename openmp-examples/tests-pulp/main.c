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

int test(int (*fun)())
{
  if(fun()) return 0;
  else {
    printf("Error\n");
    return 1;
  }
}

int main(int argc, char *argv[])
{
  unsigned n_errors = 0;

  n_errors += test_m_instrs();
  n_errors += test_dma();
  n_errors += test_floats();
  n_errors += test_hero_64();
  n_errors += test_atomic();

  printf("Testing `omp for` with static schedule ..\n");
  n_errors += test(test_omp_for_schedule_static);
  printf("Testing `omp for` with dynamic schedule ..\n");
  n_errors += test(test_omp_for_schedule_dynamic);
  printf("Testing `omp parallel for reduction` ..\n");
  n_errors += test(test_omp_parallel_for_reduction);
  printf("Testing `omp atomic` ..\n");
  n_errors += test(test_omp_atomic);
  printf("Testing `omp parallel for` with private ..\n");
  n_errors += test(test_omp_parallel_for_private);
  printf("Testing `omp parallel for` with firstprivate ..\n");
  n_errors += test(test_omp_parallel_for_firstprivate);
  printf("Testing `omp parallel for` with lastprivate ..\n");
  n_errors += test(test_omp_parallel_for_lastprivate);
  printf("Testing `omp single` ..\n");
  n_errors += test(test_omp_single);
  printf("Testing `omp critical` ..\n");
  n_errors += test(test_omp_critical);
  printf("Testing `omp master` ..\n");
  n_errors += test(test_omp_master_3);
  printf("Testing `omp barrier` ..\n");
  n_errors += test(test_omp_barrier);

  // tests for sections
  printf("Testing `omp parallel sections firstprivate` ..\n");
  n_errors += test(test_omp_parallel_sections_firstprivate);
  printf("Testing `omp parallel sections lastprivate` ..\n");
  n_errors += test(test_omp_parallel_sections_lastprivate);
  printf("Testing `omp parallel sections private` ..\n");
  n_errors += test(test_omp_parallel_sections_private);
  printf("Testing `omp parallel sections reduction\n");
  n_errors += test(test_omp_parallel_sections_reduction);
  printf("Testing `omp sections firstprivate` ..\n");
  n_errors += test(test_omp_section_firstprivate);
  printf("Testing `omp sections lastprivate` ..\n");
  n_errors += test(test_omp_section_lastprivate);
  printf("Testing `omp sections private` ..\n");
  n_errors += test(test_omp_section_private);
  printf("Testing `omp sections reduction\n");
  n_errors += test(test_omp_sections_reduction);
  
  // gcc tests
  printf("Testing gcc `omp parallel for` with static schedule with pointers ..\n");
  n_errors += test(gcc_omp_parallel_for_schedule_static);
  printf("Testing gcc `omp parallel for` with dynamic schedule with pointers ..\n");
  n_errors += test(gcc_omp_parallel_for_schedule_dynamic);
  
  printf("All OpenMP tests completed.\n");

  assert(n_errors == 0);
  return n_errors;
}
