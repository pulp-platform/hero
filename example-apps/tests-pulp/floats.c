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

#include "test.h"

unsigned test_floats()
{
  unsigned n_errors = 0;

  volatile float tmp = -1.0;
  tmp += 1.25;
  n_errors += condition_or_printf(tmp == 0.25, "Result of addition is wrong!");
  tmp *= 7.875;
  n_errors += condition_or_printf(tmp == 1.96875, "Result of multiplication is wrong!");
  tmp /= 2;
  n_errors += condition_or_printf(tmp == 0.984375, "Result of division is wrong!");
  printf("%f\n", tmp);

  printf("Floating-point tests completed.\n");
  return n_errors;
}
