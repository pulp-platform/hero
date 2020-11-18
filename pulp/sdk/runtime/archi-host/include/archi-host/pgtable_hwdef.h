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
 * Unified Interface to Architecture-Dependent Definitions Involving the Page Table Hardware
 */

#ifndef __ARCHI_HOST_PGTABLE_HWDEF_H__
#define __ARCHI_HOST_PGTABLE_HWDEF_H__

#include "archi/pulp.h"             // HOST_ARCH
#include "archi-host/phys_addr.h"   // phys_addr_t, phys_pfn_t
#include "archi-host/virt_addr.h"   // virt_addr_t, virt_pfn_t

#ifndef HOST_ARCH
    #error "Define HOST_ARCH!"
#endif
#if HOST_ARCH == ARM64
    #include "archi-host/arm64/pgtable_hwdef.h"
#elif HOST_ARCH == ARM
    #include "archi-host/arm/pgtable_hwdef.h"
#elif HOST_ARCH == RISCV64
    #include "archi-host/riscv64/pgtable_hwdef.h"
#else
    #error "Unknown host architecture!"
#endif

/**
 * Extract the address of the page for a given memory address.
 *
 * @param   addr    Virtual or physical memory address.
 *
 * @return  Page address corresponding to `addr`.
 */
extern inline unsigned page_addr(const unsigned addr);

/**
 * Get the virtual page frame number of a given virtual address.
 *
 * @param   addr    Virtual address
 *
 * @return  Virtual page frame number of `addr`.
 */
static inline virt_pfn_t virt_addr2pfn(const virt_addr_t addr)
{
    return (virt_pfn_t)(addr >> PAGE_SHIFT);
}

/**
 * Get the base address of the page with the given virtual page frame number.
 *
 * @param   pfn     Virtual page frame number
 *
 * @return  Base address of the page with virtual frame number `pfn`.
 */
static inline virt_addr_t virt_pfn2addr(const virt_pfn_t pfn)
{
    return (virt_addr_t)(pfn << PAGE_SHIFT);
}

/**
 * Get the physical page frame number of a given physical address.
 *
 * @param   addr    Physical address
 *
 * @return  Physical page frame number of `addr`.
 */
extern inline phys_pfn_t phys_addr2pfn(const phys_addr_t* const addr);

/**
 * Get the base address of the page with the given physical page frame number.
 *
 * @param   pfn     Physical page frame number
 *
 * @return  Base address of the page with physical frame number `pfn`.
 */
extern inline void phys_pfn2addr(phys_addr_t* const addr, const phys_pfn_t pfn);

#endif
