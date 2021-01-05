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

unsigned test_m_instrs()
{
  unsigned n_errors = 0;

  const int dividend  = -1491136746;
  const int divisor   = 376151960;
  int remainder;
  __asm__ volatile("rem %[remainder], %[dividend], %[divisor]"
      : [remainder] "=r" (remainder)
      : [dividend] "r" (dividend), [divisor] "r" (divisor)
      :
  );
  n_errors += condition_or_printf(remainder == -362680866, "Result of remainder is wrong");
  int quotient;
  __asm__ volatile("div %[quotient], %[dividend], %[divisor]"
      : [quotient] "=r" (quotient)
      : [dividend] "r" (dividend), [divisor] "r" (divisor)
      :
  );
  n_errors += condition_or_printf(quotient == -3, "Result of division is wrong");

  const unsigned dividend_u = 1342872853;
  const unsigned divisor_u = 654938704;
  unsigned remainder_u;
  __asm__ volatile("remu %[remainder_u], %[dividend_u], %[divisor_u]"
      : [remainder_u] "=r" (remainder_u)
      : [dividend_u] "r" (dividend_u), [divisor_u] "r" (divisor_u)
      :
  );
  n_errors += condition_or_printf(remainder_u == 32995445, "Result of unsigned remainder is wrong");
  unsigned quotient_u;
  __asm__ volatile("div %[quotient_u], %[dividend_u], %[divisor_u]"
      : [quotient_u] "=r" (quotient_u)
      : [dividend_u] "r" (dividend_u), [divisor_u] "r" (divisor_u)
      :
  );
  n_errors += condition_or_printf(quotient_u == 2, "Result of unsigned division is wrong");

  return n_errors;
}
