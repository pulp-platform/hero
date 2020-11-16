/*
 * Copyright (C) 2017 ETH Zurich and University of Bologna
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

/**
 * ARM64-Specific Handling of Physical Addresses
 */

#ifndef __ARCHI_HOST_ARM64_PHYS_ADDR_H__
#define __ARCHI_HOST_ARM64_PHYS_ADDR_H__

#include <stdint.h>     // uint8_t, uint32_t

#define PHYS_ADDR_STRLEN    (2+2+8+1)

typedef struct {
    uint32_t        lower;
    uint8_t         upper;
    const uint8_t   empty[3];
} phys_addr_t;

typedef uint32_t phys_pfn_t;

static inline int copy_phys_addr(volatile phys_addr_t* const dst,
        const volatile phys_addr_t* const src)
{
    dst->lower = *((uint32_t*)src);
    dst->upper = (uint8_t)(*((uint32_t*)src + 1) & 0xFF);

    return 0;
}

#endif
