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

unsigned test_addr_trunc()
{
  // This tests the issue discussed in
  // https://iis-git.ee.ethz.ch/hero/hero/-/merge_requests/238#note_20128
  // in which Clang would incorrectly truncate 64-bit addresses to 32-bits.
  // This is all evaluated in Clang before the optimization phase, so if
  // all works this function is statically evaluated to "return 0",
  // otherwise to "return 1".
  __host uint32_t * const l3_wide = (__host uint32_t*)0x123480000000LL;
  if ((uint64_t)l3_wide != 0x123480000000LL) {
    return 1;
  }
  return 0;
}
