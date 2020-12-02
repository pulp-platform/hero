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

int gcc_omp_parallel_for_schedule_dynamic();
int gcc_omp_parallel_for_schedule_static();

int main(int argc, char *argv[])
{
  unsigned n_errors = 0;

  n_errors += report_pass_fail(
      gcc_omp_parallel_for_schedule_static,
      "GCC `omp parallel for` with static schedule with pointers");
  n_errors += report_pass_fail(
      gcc_omp_parallel_for_schedule_dynamic,
      "GCC `omp parallel for` with dynamic schedule with pointers");

  assert(n_errors == 0);
  return n_errors;
}
