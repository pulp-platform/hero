/*
 * HERO Atomic Transactions API
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

#ifndef __HERO_ATOMIC_H__
#define __HERO_ATOMIC_H__

#include <stdint.h>

/***************************************************************************************************
 * Public API
 **************************************************************************************************/

// This API provides atomic transactions on 32-bit unsigned integers (for the maximum and minimum
// operations, signed variants exist).  Each function atomically executes the operation in its name
// on the memory pointed to by `ptr` and the provided `val` and returns the original value in
// memory.
inline static int32_t  atomic_swap  (int32_t*  const ptr, const int32_t  val);
inline static int32_t  atomic_add   (int32_t*  const ptr, const int32_t  val);
inline static int32_t  atomic_and   (int32_t*  const ptr, const int32_t  val);
inline static int32_t  atomic_or    (int32_t*  const ptr, const int32_t  val);
inline static int32_t  atomic_xor   (int32_t*  const ptr, const int32_t  val);
inline static int32_t  atomic_max   (int32_t*  const ptr, const int32_t  val);
inline static uint32_t atomic_maxu  (uint32_t* const ptr, const uint32_t val);
inline static int32_t  atomic_min   (int32_t*  const ptr, const int32_t  val);
inline static uint32_t atomic_minu  (uint32_t* const ptr, const uint32_t val);


/***************************************************************************************************
 * Implementation Internals
 **************************************************************************************************/

#ifdef __PULP__

#include <assert.h>

#define __hero_atomic_define(op, type) \
  inline static type atomic_ ## op(type * const ptr, const type val) \
  { \
    assert(((uint32_t)ptr & 0x3) == 0); /* only four-byte aligned addresses are supported */ \
    type orig; \
    __asm__ volatile("amo" #op ".w %[orig], %[val], (%[ptr])" \
        : [orig] "=r" (orig), "+m" (*ptr) \
        : [val] "r" (val), [ptr] "r" (ptr) \
    ); \
    return orig; \
  }

__hero_atomic_define(swap, int32_t)
__hero_atomic_define(add,  int32_t)
__hero_atomic_define(and,  int32_t)
__hero_atomic_define(or,   int32_t)
__hero_atomic_define(xor,  int32_t)
__hero_atomic_define(max,  int32_t)
__hero_atomic_define(maxu, uint32_t)
__hero_atomic_define(min,  int32_t)
__hero_atomic_define(minu, uint32_t)

#endif

#endif
