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
  const uint64_t addr = base + 4*omp_get_thread_num();
  const int val = 0x12345678 + omp_get_thread_num();

  hero_store_uint8(addr, (uint8_t)val);
  assert(hero_load_uint8(addr) == (uint8_t)val);
  hero_store_int8(addr, -(int8_t)val);
  assert(hero_load_int8(addr) == -(int8_t)val);

  hero_store_uint16(addr, (uint16_t)val);
  assert(hero_load_uint16(addr) == (uint16_t)val);
  hero_store_int16(addr, -(uint16_t)val);
  assert(hero_load_int16(addr) == -(uint16_t)val);

  hero_store_uint32(addr, (uint32_t)val);
  assert(hero_load_uint32(addr) == (uint32_t)val);
  hero_store_int32(addr, -(uint32_t)val);
  assert(hero_load_int32(addr) == -(uint32_t)val);
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
