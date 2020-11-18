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
 * RISCV64-Specific Definitions of the Page Table Hardware
 */

#ifndef __ARCHI_HOST_RISCV64_PGTABLE_HWDEF_H__
#define __ARCHI_HOST_RISCV64_PGTABLE_HWDEF_H__

#include "archi-host/riscv64/phys_addr.h"
#include "archi-host/virt_addr.h"

#include <errno.h>

#define PAGE_SHIFT              ((unsigned)12)
#define PAGE_SIZE               ((unsigned)(1 << PAGE_SHIFT))
#define PAGE_MASK               ((unsigned)(~((1 << PAGE_SHIFT) - 1)))

#define PTE_VALID               (1u << 0)
#define PTE_READ                (1u << 1)
#define PTE_WRITE               (1u << 2)
#define PTE_EXEC                (1u << 3)
#define PTE_USER                (1u << 4)

#define PT_SIZE                 PAGE_SIZE

#define LEVELS                  3u

#define PPN_SHIFT               10u
#define PPN_SIZE                9u

#define VPN_SHIFT               PAGE_SHIFT
#define VPN_SIZE                9u

/**
 * Check if a PTE value is valid
 *
 * @param   val Pointer to a PTE value.
 *
 * @return  1 if, according to its flags, the PTE value is valid and refers to a page; 0 if the
 *          flags are not set accordingly; negative value with an errno on errors.
 */
static inline int pte_val_is_valid(const phys_addr_t* const val)
{
    return ((*val & PTE_VALID) == PTE_VALID) && !(((*val & PTE_READ) == 0) &&
                                                  ((*val & PTE_WRITE) == PTE_WRITE));
}

/**
 * Check if a PTE value is a leaf
 *
 * @param   val Pointer to a PTE value.
 *
 * @return  1 if, according to its flags, the PTE value is valid and refers to a page; 0 if the
 *          flags are not set accordingly; negative value with an errno on errors.
 */
static inline int pte_val_is_leaf(const phys_addr_t* const val)
{
    return ((*val & PTE_READ) || (*val & PTE_EXEC));
}

/**
 * Check if the page referred to by the PTE value is readable.
 *
 * @param   val Pointer to a PTE value.
 *
 * @return  1 if the page referred to by the PTE value is accessible from user space; 0 if it is
 *          not; negative value with an errno on errors.
 */
static inline int pte_leaf_is_readable(const phys_addr_t* const val)
{
    return ((*val & PTE_READ) == PTE_READ);
}

/**
 * Check if the page referred to by the PTE value is writable.
 *
 * @param   val Pointer to a PTE value.
 *
 * @return  1 if the page referred to by the PTE value is accessible from user space; 0 if it is
 *          not; negative value with an errno on errors.
 */
static inline int pte_leaf_is_writable(const phys_addr_t* const val)
{
    return ((*val & PTE_WRITE) == PTE_WRITE);
}

/**
 * Check if the page referred to by the PTE value is accessible from user space.
 *
 * @param   val Pointer to a PTE value.
 *
 * @return  1 if the page referred to by the PTE value is accessible from user space; 0 if it is
 *          not; negative value with an errno on errors.
 */
static inline int pte_leaf_has_user_perm(const phys_addr_t* const val)
{
    return ((*val & PTE_USER) == PTE_USER);
}

/**
 * Check if a PTE value points to a page that is valid to access from user space.
 *
 * @param   val Pointer to a PTE value.
 *
 * @return  1 if the PTE value points to a page that is accessible from user space; negative value
 *          with an errno on errors.
 */
static inline int pte_leaf_is_valid(const phys_addr_t* const val)
{
    if (pte_val_is_valid(val) != 1)
        return -EINVAL;

    if (pte_leaf_has_user_perm(val) != 1)
        return -EPERM;

    return 1;
}

/**
 * Check if a PTE value points to a read-only page.
 *
 * @param   val Pointer to a PTE value.
 *
 * @return  1 if the PTE value points to a read-only page; 0 if the page is also writeable; negative
 *          value with an errno on errors.
 */
static inline int pte_val_is_rdonly_page(const phys_addr_t* const val)
{
    return ((*val & PTE_WRITE) == 0);
}

static inline unsigned page_addr(const unsigned addr)
{
    return addr & PAGE_MASK;
}

static inline phys_pfn_t phys_addr2pfn(const phys_addr_t* const addr)
{
    return (phys_pfn_t)(*addr >> PAGE_SHIFT);
}

static inline void phys_pfn2addr(phys_addr_t* const addr, const phys_pfn_t pfn)
{
    *addr = (phys_addr_t)(pfn << PAGE_SHIFT);
    return;
}

#endif
