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
 * ARM64-Specific Definitions of the Page Table Hardware
 */

#ifndef __ARCHI_HOST_ARM64_PGTABLE_HWDEF_H__
#define __ARCHI_HOST_ARM64_PGTABLE_HWDEF_H__

#include "archi-host/arm64/phys_addr.h"
#include "archi-host/virt_addr.h"

#include <errno.h>

#define PAGE_SHIFT              ((unsigned)12)
#define PGD_SHIFT               ((unsigned)30)
#define PTRS_PER_PGD            ((unsigned)512)
#define PMD_SHIFT               ((unsigned)21)
#define PMD_MASK                ((unsigned)~((1 << PMD_SHIFT) - 1))
#define PTRS_PER_PMD            ((unsigned)512)
#define PTE_SHIFT               ((unsigned)PAGE_SHIFT)
#define PTRS_PER_PTE            ((unsigned)512)

#define PT_VAL_TYPE_MASK        ((unsigned)((1 << 1) | (1 << 0)))
#define PGD_VALID_TYPE_TABLE    ((unsigned)((1 << 1) | (1 << 0)))
#define PMD_VALID_TYPE_TABLE    ((unsigned)((1 << 1) | (1 << 0)))
#define PTE_VALID_TYPE_PAGE     ((unsigned)((1 << 1) | (1 << 0)))
#define PTE_USER                ((unsigned)(1 << 6))
#define PTE_RDONLY              ((unsigned)(1 << 7))

#define PAGE_SIZE               ((unsigned)(1 << PAGE_SHIFT))
#define PAGE_MASK               (~(PAGE_SIZE - 1))

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
    return (val->lower == 0 && val->upper == 0);
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
    return ((val->lower & PT_VAL_TYPE_MASK) == PGD_VALID_TYPE_TABLE);
}

/**
 * Check if a PGD value points to a PMD.
 *
 * @param   val Pointer to a PGD value.
 *
 * @return  1 if the PGD value points to a PMD; negative value with an errno on errors.
 */
static inline int pgd_val_is_pmd_addr(const phys_addr_t* const val)
{
    if (pt_val_is_empty(val) != 0)
        return -ENXIO;

    if (pgd_val_is_type_table(val) != 1)
        return -EINVAL;

    return 1;
}

/**
 * Check if a PMD value refers to a page table.
 *
 * @param   val Pointer to a PMD value.
 *
 * @return  1 if, according to its flags, the PMD value refers to a page table; 0 if the flags are
 *          not set accordingly; negative value with an errno on errors.
 */
static inline int pmd_val_is_type_table(const phys_addr_t* const val)
{
    return ((val->lower & PT_VAL_TYPE_MASK) == PMD_VALID_TYPE_TABLE);
}

/**
 * Check if a PMD value points to a PTE.
 *
 * @param   val Pointer to a PMD value.
 *
 * @return  1 if the PMD value points to a PTE; negative value with an errno on errors.
 */
static inline int pmd_val_is_pte_addr(const phys_addr_t* const val)
{
    if (pt_val_is_empty(val) != 0)
        return -ENXIO;

    if (pmd_val_is_type_table(val) != 1)
        return -EINVAL;

    return 1;
}

/**
 * Check if a PTE value is valid and refers to a page.
 *
 * @param   val Pointer to a PTE value.
 *
 * @return  1 if, according to its flags, the PTE value is valid and refers to a page; 0 if the
 *          flags are not set accordingly; negative value with an errno on errors.
 */
static inline int pte_val_is_type_page(const phys_addr_t* const val)
{
    return ((val->lower & PT_VAL_TYPE_MASK) == PTE_VALID_TYPE_PAGE);
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
    return ((val->lower & PTE_USER) == PTE_USER);
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
    return ((val->lower & PTE_RDONLY) == PTE_RDONLY);
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
    return (virt_addr >> PGD_SHIFT) & (PTRS_PER_PGD - 1);
}

/**
 * Calculate the index to the PMD (Linux second-level page table) for a given virtual address.
 *
 * @param   virt_addr   Virtual address for which to calculate the PMD index.
 *
 * @return  The index to the PMD.
 */
static inline unsigned int pmd_index(const virt_addr_t virt_addr)
{
    return (virt_addr >> PMD_SHIFT) & (PTRS_PER_PMD - 1);
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

static inline unsigned page_addr(const unsigned addr)
{
    return addr & PAGE_MASK;
}

static inline phys_pfn_t phys_addr2pfn(const phys_addr_t* const addr)
{
    phys_pfn_t phys_pfn = \
            ((phys_pfn_t)addr->upper << (32 - PAGE_SHIFT)) | \
            ((phys_pfn_t)addr->lower >> PAGE_SHIFT);

    return phys_pfn;
}

static inline void phys_pfn2addr(phys_addr_t* const addr, const phys_pfn_t pfn)
{

    addr->lower = (uint32_t)(pfn << PAGE_SHIFT);
    addr->upper = (uint8_t)((pfn >> (32 - PAGE_SHIFT)) & 0xFF);

    return;
}

#endif
