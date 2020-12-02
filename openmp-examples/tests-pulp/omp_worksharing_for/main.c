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

int test_omp_for_schedule_dynamic();
int test_omp_for_schedule_static();
int test_omp_parallel_for_firstprivate();
int test_omp_parallel_for_lastprivate();
int test_omp_parallel_for_private();
int test_omp_parallel_for_reduction();

int main(int argc, char *argv[])
{
  unsigned n_errors = 0;

  n_errors += report_pass_fail(
      test_omp_for_schedule_static, "`omp for` with static schedule");
  n_errors += report_pass_fail(
      test_omp_for_schedule_dynamic, "`omp for` with dynamic schedule");
  n_errors += report_pass_fail(
      test_omp_parallel_for_reduction, "`omp parallel for reduction`");
  n_errors += report_pass_fail(
      test_omp_parallel_for_private, "`omp parallel for` with private");
  n_errors += report_pass_fail(
      test_omp_parallel_for_firstprivate, "`omp parallel for` with firstprivate");
  n_errors += report_pass_fail(
      test_omp_parallel_for_lastprivate, "`omp parallel for` with lastprivate");

  assert(n_errors == 0);
  return n_errors;
}
