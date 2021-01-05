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
#include "report.h"

int test_omp_parallel_sections_firstprivate();
int test_omp_parallel_sections_lastprivate();
int test_omp_parallel_sections_private();
int test_omp_parallel_sections_reduction();
int test_omp_section_firstprivate();
int test_omp_section_lastprivate();
int test_omp_section_private();
int test_omp_sections_reduction();

int main(int argc, char *argv[])
{
  unsigned n_errors = 0;

  n_errors += report_pass_fail(
      test_omp_parallel_sections_firstprivate, "`omp parallel sections firstprivate`");
  n_errors += report_pass_fail(
      test_omp_parallel_sections_lastprivate, "`omp parallel sections lastprivate`");
  n_errors += report_pass_fail(
      test_omp_parallel_sections_private, "`omp parallel sections private`");
  n_errors += report_pass_fail(
      test_omp_parallel_sections_reduction, "`omp parallel sections reduction`");
  n_errors += report_pass_fail(
      test_omp_section_firstprivate, "`omp sections firstprivate`");
  n_errors += report_pass_fail(
      test_omp_section_lastprivate, "`omp sections lastprivate`");
  n_errors += report_pass_fail(
      test_omp_section_private, "`omp sections private`");
  n_errors += report_pass_fail(
      test_omp_sections_reduction, "`omp sections reduction`");

  assert(n_errors == 0);
  return n_errors;
}
