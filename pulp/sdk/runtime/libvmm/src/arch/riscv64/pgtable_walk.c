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

#include "archi-host/riscv64/pgtable_hwdef.h"
#include "hal/rab/rab_v1.h"
#include "rt/rt_alloc.h"    // rt_alloc(), rt_free()
#include "rt/rt_debug.h"
#include "vmm/config.h"
#include "vmm/host.h"

#include "stdio.h"

#define PTE_BPTR    (VMM_PGD_BPTR + PT_SIZE)
#define PTE_EPTR    (PTE_BPTR + PT_SIZE)

#ifdef PTW_MEAS_PERF_FINE
    #define PTW_MEAS_PERF
#endif
#ifdef PTW_MEAS_PERF
    #define MEAS_PERF
#endif

#ifndef LOG_LVL_PTW
    #define LOG_LVL_PTW RT_LOG_DEBUG
#endif

static inline int config_pt_rab_slice(const phys_addr_t* const pt_addr)
{
    return config_rab_slice((virt_addr_t)PTE_BPTR, (virt_addr_t)PTE_EPTR, pt_addr, RAB_CFG_PTE_PTR,
                            1, 0);
}

/**
 * Get physical address of page through PTE.
 *
 * @param   pte             Page table entry record.
 * @param   virt_addr       Virtual address to be translated.
 * @param   level           Level in page table at which page is retrieved (0 for normal pages).
 * @param   page_addr_ptr   Pointer to which the physical address of the page is returned.
 * @param   page_rdonly     Pointer to a byte that shall be set to `1` if the page is read-only.
 *
 * @return  0 on success (in this case, the output parameters are set to valid values as described
 *          above); negative value with an errno on errors (in this case, the value of the output
 *          parameters is undefined).
 */
static inline int get_page_phys_addr(const phys_addr_t pte,
                                     const virt_addr_t virt_addr,
                                     const int level,
                                     phys_addr_t* const page_addr_ptr,
                                     unsigned char* const page_rdonly) {
    // check valid superpage
    if((pte >> PPN_SHIFT) & ((1ull << (PPN_SIZE * level)) - 1)) {
        return -EFAULT;
    }

    // check accessible from user space
    if(!pte_leaf_is_readable(&pte) || !pte_leaf_has_user_perm(&pte)) {
        return -EFAULT;
    }

    // find address
    *page_addr_ptr = ((pte >> PPN_SHIFT) & ((1ull << (PPN_SIZE * LEVELS)) - 1)) |
        ((virt_addr >> VPN_SHIFT) & ((1ull << (VPN_SIZE * level)) - 1));
    *page_addr_ptr <<= PAGE_SHIFT;

    *page_rdonly = !pte_leaf_is_writable(&pte);
    return 0;
}

/**
 * Get physical address of next level page table from PTE.
 *
 * @param   pte             Page table entry record.
 * @param   pte_phys_addr   Pointer through which the physical page table address is returned.
 *
 * @return  0 on success (in this case, `pte_phys_addr` contains the physical address of the PTE
 *          after this function returns); negative value with an errno on errors (in this case, the
 *          value of `pte_phys_addr` is undefined after this function returns).
 */
static inline int get_pt_addr(const phys_addr_t pte,
                              phys_addr_t* const pt_addr) {
    *pt_addr = (pte >> PPN_SHIFT);
    *pt_addr <<= PAGE_SHIFT;
    return 0;
}

/**
 * Get PTE from offset to page table
 *
 * @param   pte_ptr         Pointer to the page table base address
 * @param   virt_addr       Virtual address to be translated.
 * @param   level           Level of the current page table
 * @param   pte_ptr         Pointer to which the page table entry is returned
 * @param   leaf            Pointer to a byte that shall be set to `1` if the PTE is a leaf.
 *
 * @return  0 on success (in this case, the output parameters are set to valid values as described
 *          above); negative value with an errno on errors (in this case, the value of the output
 *          parameters is undefined).
 */
static inline int get_pte(const phys_addr_t* pt_ptr,
                          const virt_addr_t virt_addr,
                          const int level,
                          phys_addr_t* const pte_ptr,
                          unsigned char* const leaf) {
#ifdef PTW_MEAS_PERF_FINE
    perf_cycles_push();
#endif

    int offset = 0;
    // FIXME: the higher bits should be zero in real virtual address else we could not translate
    if ((VPN_SIZE * (level + 1) + VPN_SHIFT) <= 8 * sizeof(virt_addr_t)) {
        offset = (virt_addr >> (VPN_SIZE * level + VPN_SHIFT)) & ((1u << VPN_SIZE) - 1);
    }
    copy_phys_addr(pte_ptr, pt_ptr + offset);

#ifdef PTW_MEAS_PERF_FINE
    perf_cycles_push();
#endif

    if(!pte_val_is_valid(pte_ptr)) {
        return -EFAULT;
    }

#ifdef PTW_MEAS_PERF_FINE
    perf_cycles_push();
#endif

    *leaf = pte_val_is_leaf(pte_ptr);
    return 0;
}

int virt_addr_to_page_phys_addr(const virt_addr_t virt_addr,
        phys_addr_t* const page_phys_addr_ptr, unsigned char* const page_rdonly)
{
    int ret = 0;

    phys_addr_t* pt_ptr = VMM_PGD_BPTR;
    int level = LEVELS - 1;

    while(1) {
#ifdef PTW_MEAS_PERF
        perf_cycles_push();
#endif

        phys_addr_t pte;
        unsigned char leaf;
        ret = get_pte(pt_ptr, virt_addr, level, &pte, &leaf);

        if(ret < 0) {
#if RT_LOG_ERRORS(LOG_LVL_PTW)
            rt_error("Failed to find PTE at level %d with errno %d!\n", level, -ret);
#endif
            return ret;
        }

        if(leaf) {
            ret = get_page_phys_addr(pte, virt_addr, level, page_phys_addr_ptr, page_rdonly);
            if(ret < 0) {
#if RT_LOG_ERRORS(LOG_LVL_PTW)
                rt_error("Failed to retrieve page PA from leaf PTE at level %d with errno %d!\n",
                         level, -ret);
#endif
                return ret;
            }

#if RT_LOG_DEBUGS(LOG_LVL_PTW)
            {
                const size_t buf_size = sizeof(char) * PHYS_ADDR_STRLEN;
                char* const buf = rt_alloc(RT_ALLOC_CL_DATA, buf_size);
                if (buf != NULL) {
                    sprint_phys_addr(buf, page_phys_addr_ptr);
                    rt_debug("Read leaf PTE at level %d, got host page PA at %s.\n", level, buf);
                    rt_free(RT_ALLOC_CL_DATA, buf, buf_size);
                }
            }
#endif

#ifdef PTW_MEAS_PERF
            perf_cycles_push();
#endif

            return 0;
        }

        --level;
        if(level < 0) {
            return -EFAULT;
        }

        phys_addr_t host_pt_addr;
        ret = get_pt_addr(pte, &host_pt_addr);
        if(ret < 0) {
#if RT_LOG_ERRORS(LOG_LVL_PTW)
            rt_error("Failed to find page table at level %d with errno %d!\n", level, -ret);
#endif
            return ret;
        }

#if RT_LOG_DEBUGS(LOG_LVL_PTW)
        {
            const size_t buf_size = sizeof(char) * PHYS_ADDR_STRLEN;
            char* const buf = rt_alloc(RT_ALLOC_CL_DATA, buf_size);
            if (buf != NULL) {
                sprint_phys_addr(buf, &host_pt_addr);
                rt_debug("Read PTE, got host page table PA of level %d at %s.\n", level, buf);
                rt_free(RT_ALLOC_CL_DATA, buf, buf_size);
            }
        }
#endif

#ifdef PTW_MEAS_PERF
        perf_cycles_push();
#endif

        ret = config_pt_rab_slice(&host_pt_addr);
        if(ret < 0) {
#if RT_LOG_ERRORS(LOG_LVL_PTW)
            rt_error("Failed to setup RAB slice for PTE at level %d with errno %d!\n", level, -ret);
#endif
            return ret;
        }
        pt_ptr = PTE_BPTR;
    }

    return -EFAULT;
}
