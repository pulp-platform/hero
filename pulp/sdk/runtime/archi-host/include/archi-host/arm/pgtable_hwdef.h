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
 * ARM-Specific Definitions of the Page Table Hardware
 */

#ifndef __ARCHI_HOST_ARM_PGTABLE_HWDEF_H__
#define __ARCHI_HOST_ARM_PGTABLE_HWDEF_H__

#include "archi-host/arm/phys_addr.h"
#include "archi-host/virt_addr.h"

#include <errno.h>

/**
 * Source: Linux kernel files
 *  - arch/arm/include/asm/page.h
 *  - arch/arm/include/asm/pgtable-2level.h
 */
#define PAGE_SHIFT              ((unsigned)12)
#define PGD_SHIFT               ((unsigned)21)
#define PGD_MASK                ((unsigned)~((1 << PGD_SHIFT) - 1))
#define PTRS_PER_PGD            ((unsigned)2048)
#define PTRS_PER_PMD            ((unsigned)1)
#define PTE_SHIFT               ((unsigned)PAGE_SHIFT)
#define PTRS_PER_PTE            ((unsigned)512)

#define PT_VAL_TYPE_MASK        ((unsigned)((1 << 1) | (1 << 0)))
#define PGD_VALID_TYPE_TABLE    ((unsigned)(1 << 1))
#define PTE_VALID_TYPE_PAGE     ((unsigned)((1 << 1) | (1 << 0)))
#define PTE_USER                ((unsigned)(1 << 8))
#define PTE_RDONLY              ((unsigned)(1 << 7))

#define PAGE_SIZE               ((unsigned)(1 << PAGE_SHIFT))
#define PAGE_MASK               ((unsigned)(~((1 << PAGE_SHIFT) - 1)))

/**
 * Check if a page table value is empty.
 *
 * @param   val Pointer to a page table value.
 *
 * @return  1 if the page table value is empty; 0 if it contains data; negative value with an errno
 *          on errors.
 */
static inline int pt_val_is_empty(const phys_addr_t* const val)
{
    return (val == 0);
}

/**
 * Check if a PGD value refers to a page table.
 *
 * @param   val Pointer to a PGD value.
 *
 * @return  1 if, according to its flags, the PGD value refers to a page table; 0 if the flags are
 *          not set accordingly; negative value with an errno on errors.
 */
static inline int pgd_val_is_type_table(const phys_addr_t* const val)
{
    // Same check as in `bad_pmd` in `gup.c` in the Linux kernel: if bit 1 is set, the entry is
    // considered bad.
    return (((unsigned int)val & PGD_VALID_TYPE_TABLE) ? 0 : 1);
}

/**
 * Calculate the index to the PGD (Linux first-level page table) for a given virtual address.
 *
 * @param   virt_addr   Virtual address for which to calculate the PGD index.
 *
 * @return  The index to the PGD.
 */
static inline unsigned int pgd_index(const virt_addr_t virt_addr)
{
    // PGD entries are 64 bit wide, but only the lower 32 bit contain data that are relevant for us.
    return ((virt_addr >> PGD_SHIFT) & (PTRS_PER_PGD - 1)) << 1;
}

/**
 * Calculate the index to the PTE (Linux third-level page table) for a given virtual address.
 *
 * @param   virt_addr   Virtual address for which to calculate the PTE index.
 *
 * @return  The index to the PTE.
 */
static inline unsigned int pte_index(const virt_addr_t virt_addr)
{
    return (virt_addr >> PTE_SHIFT) & (PTRS_PER_PTE - 1);
}

/**
 * Check if a PMD value points to a PTE.
 *
 * @param   val Pointer to a PMD value.
 *
 * @return  1 if the PMD value points to a PTE; negative value with an errno on errors.
 */
static inline int pgd_val_is_pte_addr(const phys_addr_t* const val)
{
    if (pt_val_is_empty(val) != 0)
        return -ENXIO;

    if (pgd_val_is_type_table(val) != 1)
        return -EINVAL;

    return 1;
}

/**
 * Check if a PTE value is valid and refers to a page.  This is done by checking the VALID and YOUNG
 * bit of the PTE.
 *
 * @param   val Pointer to a PTE value.
 *
 * @return  1 if, according to its flags, the PTE value is valid and refers to a page; 0 if the
 *          flags are not set accordingly; negative value with an errno on errors.
 */
static inline int pte_val_is_type_page(const phys_addr_t* const val)
{
    return ((*val & PT_VAL_TYPE_MASK) == PTE_VALID_TYPE_PAGE);
}

/**
 * Check if the page referred to by the PTE value is accessible from user space.
 *
 * @param   val Pointer to a PTE value.
 *
 * @return  1 if the page referred to by the PTE value is accessible from user space; 0 if it is
 *          not; negative value with an errno on errors.
 */
static inline int pte_val_has_user_perm(const phys_addr_t* const val)
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
static inline int pte_val_is_valid_page_addr(const phys_addr_t* const val)
{
    if (pt_val_is_empty(val))
        return -ENXIO;

    if (pte_val_is_type_page(val) != 1)
        return -EINVAL;

    if (pte_val_has_user_perm(val) != 1)
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
    return ((*val & PTE_RDONLY) == PTE_RDONLY);
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
