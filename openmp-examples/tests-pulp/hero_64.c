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
#include <omp.h>
#include <stdint.h>
#include <stdio.h>
#include "hero_64.h"

inline static void check_addr(const uint64_t base)
{
  const uint64_t addr = base + 8*omp_get_thread_num();
  const uint64_t val = 0x1234567812345678 + omp_get_thread_num();

  *(uint8_t*)addr = 0;
  hero_store_uint8(addr, (uint8_t)val);
  assert(hero_load_uint8(addr) == (uint8_t)val);

  *(uint16_t*)addr = 0;
  hero_store_uint16(addr, (uint16_t)val);
  assert(hero_load_uint16(addr) == (uint16_t)val);

  *(uint32_t*)addr = 0;
  hero_store_uint32(addr, (uint32_t)val);
  assert(hero_load_uint32(addr) == (uint32_t)val);

  *(uint64_t*)addr = 0;
  hero_store_uint64(addr, (uint64_t)val);
  assert(hero_load_uint64(addr) == (uint64_t)val);
}

unsigned test_hero_64()
{
  const uint64_t l1_base        = 0x0000000010032000;
  const uint64_t l1_alias_base  = 0x000000001B032000;
  const uint64_t l2_base        = 0x000000001C032000;
  #pragma omp parallel
  {
    check_addr(l1_base);
    check_addr(l1_alias_base);
    check_addr(l2_base);
  }
  printf("Tests passed on all threads!\n");

  return 0;
}
