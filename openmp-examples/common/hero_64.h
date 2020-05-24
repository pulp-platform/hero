/*
 * HERO 64-bit Addressing API
 *
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

#ifndef __HERO_64_H__
#define __HERO_64_H__

#include <stdint.h>

/***************************************************************************************************
 * Public API
 **************************************************************************************************/

// This API provides loads and stores of 64-bit, 32-bit, 16-bit, and 8-bit unsigned integers to
// 64-bit addresses.  Each load and store exists in two variants:
// -  The blocking functions (no suffix) do not return until the memory access has succeeded.  Loads
//    return the loaded value.
// -  The non-blocking functions (`_noblock` suffix) return 0 on success and a non-zero value on
//    failure.  Loads pass the loaded value back through the `val` pointer.  The value stored in
//    `val` after a failing load is undefined.  It is illegal to let `val` point to a memory
//    location that might be unaccessible; violating this leads to undefined behavior. Moreover,
//    `val` has to be a native 32-bit device pointer as the load cannot be replaced recursively.
// Natively aligned 32-bit, 16-bit, and 8-bit memory accesses give rise to a single memory access
// operation and are thus single-copy atomic.  Unaligned or 64-bit memory accesses give rise to at
// least two memory access operations, and such loads from a memory location for which a race exists
// return an undefined value.
// For 64-bit memory accesses, the lower 32 bit are accessed before the upper 32 bit.  For the
// `uint64_noblock` functions, the upper 32 bit are always accessed (i.e., even if access to the
// lower 32 bit has failed), and the return value is the bitwise OR of the two `uint32_noblock`
// return values.
inline static __attribute__((used)) uint64_t  hero_load_uint64          (const uint64_t addr);
inline static __attribute__((used)) void      hero_store_uint64         (const uint64_t addr,
                                                                         const uint64_t val);
inline static __attribute__((used)) int       hero_load_uint64_noblock  (const uint64_t addr,
                                                                         __device uint64_t* const val);
inline static __attribute__((used)) int       hero_store_uint64_noblock (const uint64_t addr,
                                                                         const uint64_t val);
inline static __attribute__((used)) uint32_t  hero_load_uint32          (const uint64_t addr);
inline static __attribute__((used)) void      hero_store_uint32         (const uint64_t addr,
                                                                         const uint32_t val);
inline static __attribute__((used)) int       hero_load_uint32_noblock  (const uint64_t addr,
                                                                         __device uint32_t* const val);
inline static __attribute__((used)) int       hero_store_uint32_noblock (const uint64_t addr,
                                                                         const uint32_t val);
inline static __attribute__((used)) uint16_t  hero_load_uint16          (const uint64_t addr);
inline static __attribute__((used)) void      hero_store_uint16         (const uint64_t addr,
                                                                         const uint16_t val);
inline static __attribute__((used)) int       hero_load_uint16_noblock  (const uint64_t addr,
                                                                         __device uint16_t* const val);
inline static __attribute__((used)) int       hero_store_uint16_noblock (const uint64_t addr,
                                                                         const uint16_t val);
inline static __attribute__((used)) uint8_t   hero_load_uint8           (const uint64_t addr);
inline static __attribute__((used)) void      hero_store_uint8          (const uint64_t addr,
                                                                         const uint8_t val);
inline static __attribute__((used)) int       hero_load_uint8_noblock   (const uint64_t addr,
                                                                         __device uint8_t* const val);
inline static __attribute__((used)) int       hero_store_uint8_noblock  (const uint64_t addr,
                                                                         const uint8_t val);

/***************************************************************************************************
 * Implementation Internals
 **************************************************************************************************/

#ifdef __PULP__

#pragma clang diagnostic push
// NOTE: Clang currently incorrectly labels casts from integers to device pointers as being of different size
#pragma clang diagnostic ignored "-Wint-to-pointer-cast"

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h> // abort()

#define __ADDREXT_REG 0x10200BF8
#define __TRYX_RES_REG 0x10200BFC

inline static uint32_t __upper32(const uint64_t dw)
{
  return (uint32_t)(dw >> 32);
}

inline static uint32_t __lower32(const uint64_t dw)
{
  return (uint32_t)dw;
}

inline static void __loop_forever()
{
  while (1) {
    __asm__ volatile("nop" : : : );
  }
}

#define __hero_64_noblock_pre(data_t) \
  const uint32_t upper = __upper32(addr); \
  __device volatile data_t* const lower = (__device volatile data_t*)__lower32(addr); \
  uint32_t tryx_res; \
  uint32_t mstatus;

#define __hero_64_noblock_post \
  return (int)(tryx_res & 0xF);

#define __hero_64_op_suffix(type, bits) __hero_64_op_suffix_ ## bits(type)
#define __hero_64_op_suffix_uint "u"
#define __hero_64_op_suffix_int
#define __hero_64_op_suffix_32(type) "w"
#define __hero_64_op_suffix_16(type) "h" __hero_64_op_suffix_ ## type
#define __hero_64_op_suffix_8(type)  "b" __hero_64_op_suffix_ ## type

#define __hero_64_disable_mirq_asm    "csrrci %[mstatus], 0x300, 3"
#define __hero_64_restore_mstatus_asm "csrrw x0, 0x300, %[mstatus]"

#define __hero_64_define_load_noblock(bits) \
  inline static int hero_load_uint ## bits ## _noblock(\
      const uint64_t addr, __device uint ## bits ## _t* const val) { \
    __hero_64_noblock_pre(uint ## bits ## _t) \
    /*printf("# loading 0x%llx\n", addr); */  \
    /*val = *(__device uint ## bits ##_t *)addr; */              \
    /*printf("# value 0x%llx\n", 0);              */              \
    /*return 0; */                                                      \
    __device static volatile uint32_t* const addrext_reg = (__device uint32_t*)__ADDREXT_REG; \
    uint ## bits ## _t reg; \
    __asm__ volatile( \
        __hero_64_disable_mirq_asm "\n\t" \
        "sw %[upper], 0(%[addrext_reg])\n\t" /* set address extension register */ \
        "l" __hero_64_op_suffix(uint, bits) " %[reg], 0(%[lower])\n\t" /* do actual load */ \
        "lw %[tryx_res], 4(%[addrext_reg])\n\t" /* read the tryx result */ \
        __hero_64_restore_mstatus_asm \
        : [reg] "=&r" (reg), [tryx_res] "=r" (tryx_res), [mstatus] "+&r" (mstatus) \
        : [upper] "r" (upper), [addrext_reg] "r" (addrext_reg), [lower] "r" (lower) \
        : "memory" \
    ); \
    /*printf("# value 0x%llx\n", (uint64_t)reg);  */  \
    *val = reg;                                       \
    return 0; \
    __hero_64_noblock_post \
  }

#define __hero_64_define_store_noblock(bits) \
  inline static int hero_store_uint ## bits ## _noblock(\
      const uint64_t addr, const uint ## bits ## _t val) { \
    __hero_64_noblock_pre(uint ## bits ## _t) \
      /*printf("# storing 0x%llx %d\n", addr, (int32_t) val);    */     \
    __device static volatile uint32_t* const addrext_reg = (__device uint32_t*)__ADDREXT_REG; \
    __asm__ volatile( \
        __hero_64_disable_mirq_asm "\n\t" \
        "sw %[upper], 0(%[addrext_reg])\n\t" /* set address extension register */ \
        "s" __hero_64_op_suffix(int, bits) " %[val], 0(%[lower])\n\t" /* do actual store */ \
        "lw %[tryx_res], 4(%[addrext_reg])\n\t" /* read the tryx result */ \
        __hero_64_restore_mstatus_asm \
        : [tryx_res] "=r" (tryx_res), [mstatus] "+&r" (mstatus) \
        : [upper] "r" (upper), [addrext_reg] "r" (addrext_reg), \
          [val] "r" (val), [lower] "r" (lower) \
        : "memory" \
    ); \
    return 0; \
    __hero_64_noblock_post \
  }

// if (res != 0) { \
//   printf("ERROR: Memory access violation at 0x%08x%08x!\n", __upper32(addr), __lower32(addr)); \
//   abort(); \
// }

#define __hero_64_check_mem_access \
  // TODO: handle misses

#define __hero_64_define_load(size) \
  inline static uint ## size ## _t hero_load_uint ## size(const uint64_t addr) { \
    uint ## size ## _t val; \
    const int res = hero_load_uint ## size ## _noblock(addr, (__device uint ## size ## _t*)&val); \
    __hero_64_check_mem_access \
    return val; \
  }

#define __hero_64_define_store(size) \
  inline static void hero_store_uint ## size (const uint64_t addr, const uint ## size ## _t val) { \
    const int res = hero_store_uint ## size ## _noblock(addr, val); \
    __hero_64_check_mem_access \
  }

#define __hero_64_define(size) \
  __hero_64_define_load_noblock(size) \
  __hero_64_define_load(size) \
  __hero_64_define_store_noblock(size) \
  __hero_64_define_store(size)

// FIXME: investigate error when this is put at start of the file
#pragma omp declare target
__hero_64_define(32)
__hero_64_define(16)
__hero_64_define( 8)

uint64_t hero_load_uint64(const uint64_t addr)
{
  const uint32_t lower = hero_load_uint32(addr);
  const uint32_t upper = hero_load_uint32(addr+4);
  uint64_t ret_val = ((uint64_t)upper << 32) | lower;
  //printf("RET: %x %x %llx\n", lower, upper, ret_val);
  return ret_val;
}

void hero_store_uint64(const uint64_t addr, const uint64_t val)
{
  const uint32_t lower = (uint32_t)val;
  hero_store_uint32(addr, lower);
  const uint32_t upper = (uint32_t)(val >> 32);
  hero_store_uint32(addr+4, upper);
}

int hero_load_uint64_noblock(const uint64_t addr, __device uint64_t* const val)
{
  __device uint32_t* const lower = (__device uint32_t*)val;
  const int res_lower = hero_load_uint32_noblock(addr, lower);
  __device uint32_t* const upper = lower + 1;
  const int res_upper = hero_load_uint32_noblock(addr+4, upper);
  return res_lower | res_upper;
}

int hero_store_uint64_noblock(const uint64_t addr, const uint64_t val)
{
  const uint32_t lower = (uint32_t)val;
  const int res_lower = hero_store_uint32_noblock(addr, lower);
  const uint32_t upper = (uint32_t)(val >> 32);
  const int res_upper = hero_store_uint32_noblock(addr+4, upper);
  return res_lower | res_upper;
}
#pragma omp end declare target

#pragma clang diagnostic pop

#endif

#endif
