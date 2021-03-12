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
#include <stdint.h>
#include <stdio.h>
#include "hero_64.h"
#include "test.h"

inline static void check_addr(const uint64_t base)
{
  const uint64_t addr = base + 8*omp_get_thread_num();
  const uint64_t val = 0x8765432112345678 + omp_get_thread_num();

  hero_store_uint8(addr, (uint8_t)val + 0x11);
  assert(hero_load_uint8(addr) == (uint8_t)val + 0x11);

  hero_store_uint16(addr, (uint16_t)val + 0x2222);
  assert(hero_load_uint16(addr) == (uint16_t)val + 0x2222);

  hero_store_uint32(addr, (uint32_t)val + 0x33333333);
  assert(hero_load_uint32(addr) == (uint32_t)val + 0x33333333);

  hero_store_uint64(addr, (uint64_t)val + 0x4444444444444444);
  assert(hero_load_uint64(addr) == (uint64_t)val + 0x4444444444444444);
}

inline static void check_fail(const uint64_t base)
{
  const uint64_t addr = base + 8*omp_get_thread_num();
  uint64_t dummy;
  assert(hero_store_uint8_noblock(addr, dummy) != 0);
  assert(hero_load_uint8_noblock(addr, (__device uint8_t*)&dummy) != 0);
  assert(hero_store_uint16_noblock(addr, dummy) != 0);
  assert(hero_load_uint16_noblock(addr, (__device uint16_t*)&dummy) != 0);
  assert(hero_store_uint32_noblock(addr, dummy) != 0);
  assert(hero_load_uint32_noblock(addr, (__device uint32_t*)&dummy) != 0);
  assert(hero_store_uint64_noblock(addr, dummy) != 0);
  assert(hero_load_uint64_noblock(addr, (__device uint64_t*)&dummy) != 0);
}

unsigned test_hero_64()
{
  for (uint32_t offset = 0; offset < 8; offset++) {
    printf("Testing accesses with offset %d...\n", offset);
    #pragma omp parallel
    {
      check_addr(test_l1_base() + offset);
      check_addr(test_l1_alias_base() + offset);
      check_addr(test_l1_other_base() + offset);
      check_addr(test_l2_base() + offset);
      check_addr(test_dram_base() + offset);
      check_addr(test_dram_64bit_addr() + offset);
    }
    printf("Testing failure response to zero page with offset %d...\n", offset);
    #pragma omp parallel
    {
      check_fail(offset);
    }
    printf("Tests with offset %d passed on all threads.\n", offset);
  }
  return 0;
}
