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
 * ARM-Specific Handling of Physical Addresses
 */

#ifndef __ARCHI_HOST_ARM_PHYS_ADDR_H__
#define __ARCHI_HOST_ARM_PHYS_ADDR_H__

#include <stdint.h>     // uint32_t

#define PHYS_ADDR_STRLEN    (2+8+1)

typedef uint32_t phys_addr_t;
typedef uint32_t phys_pfn_t;

static inline int copy_phys_addr(volatile phys_addr_t* const dst,
        const volatile phys_addr_t* const src)
{
    *dst = *src;
    return 0;
}

#endif
