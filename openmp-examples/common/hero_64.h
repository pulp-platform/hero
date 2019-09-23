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

/***************************************************************************************************
 * Public API
 **************************************************************************************************/

// This API provides loads and stores of 32-bit, 16-bit, and 8-bit signed and unsigned integers to
// 64-bit addresses.  Each load and store exists in two variants:
// -  The blocking functions (no suffix) do not return until the memory access has succeeded.  Loads
//    return the loaded value.
// -  The non-blocking functions (`_noblock` suffix) return 0 on success and a non-zero value on
//    failure.  Loads pass the loaded value back through the `val` pointer.
inline static __attribute__((used)) uint32_t  hero_load_uint32          (const uint64_t addr);
inline static __attribute__((used)) void      hero_store_uint32         (const uint64_t addr, const uint32_t val);
inline static __attribute__((used)) int       hero_load_uint32_noblock  (const uint64_t addr, uint32_t* const val);
inline static __attribute__((used)) int       hero_store_uint32_noblock (const uint64_t addr, const uint32_t val);
inline static __attribute__((used)) int32_t   hero_load_int32           (const uint64_t addr);
inline static __attribute__((used)) void      hero_store_int32          (const uint64_t addr, const int32_t val);
inline static __attribute__((used)) int       hero_load_int32_noblock   (const uint64_t addr, int32_t* const val);
inline static __attribute__((used)) int       hero_store_int32_noblock  (const uint64_t addr, const int32_t val);
inline static __attribute__((used)) uint16_t  hero_load_uint16          (const uint64_t addr);
inline static __attribute__((used)) void      hero_store_uint16         (const uint64_t addr, const uint16_t val);
inline static __attribute__((used)) int       hero_load_uint16_noblock  (const uint64_t addr, uint16_t* const val);
inline static __attribute__((used)) int       hero_store_uint16_noblock (const uint64_t addr, const uint16_t val);
inline static __attribute__((used)) int16_t   hero_load_int16           (const uint64_t addr);
inline static __attribute__((used)) void      hero_store_int16          (const uint64_t addr, const int16_t val);
inline static __attribute__((used)) int       hero_load_int16_noblock   (const uint64_t addr, int16_t* const val);
inline static __attribute__((used)) int       hero_store_int16_noblock  (const uint64_t addr, const int16_t val);
inline static __attribute__((used)) uint8_t   hero_load_uint8           (const uint64_t addr);
inline static __attribute__((used)) void      hero_store_uint8          (const uint64_t addr, const uint8_t val);
inline static __attribute__((used)) int       hero_load_uint8_noblock   (const uint64_t addr, uint8_t* const val);
inline static __attribute__((used)) int       hero_store_uint8_noblock  (const uint64_t addr, const uint8_t val);
inline static __attribute__((used)) int8_t    hero_load_int8            (const uint64_t addr);
inline static __attribute__((used)) void      hero_store_int8           (const uint64_t addr, const int8_t val);
inline static __attribute__((used)) int       hero_load_int8_noblock    (const uint64_t addr, int8_t* const val);
inline static __attribute__((used)) int       hero_store_int8_noblock   (const uint64_t addr, const int8_t val);


/***************************************************************************************************
 * Implementation Internals
 **************************************************************************************************/

inline static void __mem_fence()
{
  __asm__ __volatile__("" : : : "memory");
}

#if __riscv_xlen == 32 // FIXME: properly check for host/accelerator toolchain here

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

static volatile uint32_t* const __addrext_reg = (uint32_t*)0x10200BF8;
static volatile uint32_t* const __tryx_res_reg = (uint32_t*)0x10200BFC;

inline static void __mstatus_write(const uint32_t val)
{
  __asm__ volatile (
      "csrrw x0, 0x300, %[val]"
      : /* no outputs */
      : [val] "r" (val)
  );
}

inline static uint32_t __disable_mirq()
{
  uint32_t mstatus;
  __asm__ volatile (
      "csrrci %[mstatus], 0x300, 3"
      : [mstatus] "=r" (mstatus)
      : /* no inputs */
  );
  return mstatus;
}

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
  volatile data_t* const lower = (volatile data_t*)__lower32(addr); \
  uint32_t tryx_res; \
  const uint32_t mstatus = __disable_mirq(); \
  __mem_fence();

#define __hero_64_noblock_post \
  __mem_fence(); \
  __mstatus_write(mstatus); \
  return (int)(tryx_res & 0xF);

#define __hero_64_op_suffix(type, bits) __hero_64_op_suffix_ ## bits(type)
#define __hero_64_op_suffix_uint "u"
#define __hero_64_op_suffix_int
#define __hero_64_op_suffix_32(type) "w"
#define __hero_64_op_suffix_16(type) "h" __hero_64_op_suffix_ ## type
#define __hero_64_op_suffix_8(type)  "b" __hero_64_op_suffix_ ## type

#define __hero_64_define_load_noblock(type, bits) \
  inline static int hero_load_ ## type ## bits ## _noblock(\
      const uint64_t addr, type ## bits ## _t* const val) { \
    __hero_64_noblock_pre(type ## bits ## _t) \
    type ## bits ## _t reg; \
    __asm__ volatile( \
        "sw %[upper], 0(%[__addrext_reg])\n\t" /* set address extension register */ \
        "l" __hero_64_op_suffix(type, bits) " %[reg], 0(%[lower])\n\t" /* do actual load */ \
        "lw %[tryx_res], 4(%[__addrext_reg])" /* read the tryx result */ \
        : [reg] "=&r" (reg), [tryx_res] "=r" (tryx_res) \
        : [upper] "r" (upper), [__addrext_reg] "r" (__addrext_reg), [lower] "r" (lower) \
        : "memory" \
    ); \
    *val = reg; \
    __hero_64_noblock_post \
  }

#define __hero_64_define_store_noblock(type, bits) \
  inline static int hero_store_ ## type ## bits ## _noblock(\
      const uint64_t addr, const type ## bits ## _t val) { \
    __hero_64_noblock_pre(type ## bits ## _t) \
    __asm__ volatile( \
        "sw %[upper], 0(%[__addrext_reg])\n\t" /* set address extension register */ \
        "s" __hero_64_op_suffix(int, bits) " %[val], 0(%[lower])\n\t" /* do actual store */ \
        "lw %[tryx_res], 4(%[__addrext_reg])" /* read the tryx result */ \
        : [tryx_res] "=r" (tryx_res) \
        : [upper] "r" (upper), [__addrext_reg] "r" (__addrext_reg), \
          [val] "r" (val), [lower] "r" (lower) \
        : "memory" \
    ); \
    __hero_64_noblock_post \
  }

#define __hero_64_check_mem_access \
  if (res != 0) { \
    printf("ERROR: Memory access violation at 0x%08x%08x!\n", __upper32(addr), __lower32(addr)); \
    __loop_forever(); \
  }
  // TODO: handle misses (or properly abort execution if misses cannot be handled?)

#define __hero_64_define_load(type) \
  inline static type ## _t hero_load_ ## type (const uint64_t addr) { \
    type ## _t val; \
    const int res = hero_load_ ## type ## _noblock(addr, &val); \
    __hero_64_check_mem_access \
    return val; \
  }

#define __hero_64_define_store(type) \
  inline static void hero_store_ ## type (const uint64_t addr, const type ## _t val) { \
    const int res = hero_store_ ## type ## _noblock(addr, val); \
    __hero_64_check_mem_access \
  }

#define __hero_64_define(type, size) \
  __hero_64_define_load_noblock(type, size) \
  __hero_64_define_load(type ## size) \
  __hero_64_define_store_noblock(type, size) \
  __hero_64_define_store(type ## size)

__hero_64_define(uint, 32)
__hero_64_define( int, 32)
__hero_64_define(uint, 16)
__hero_64_define( int, 16)
__hero_64_define(uint,  8)
__hero_64_define( int,  8)

#endif

#endif
