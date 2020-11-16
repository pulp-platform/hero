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

#include "archi-host/arm64/pgtable_hwdef.h"
#include "hal/rab/rab_v1.h"
#include "rt/rt_alloc.h"    // rt_alloc(), rt_free()
#include "rt/rt_debug.h"
#include "vmm/config.h"
#include "vmm/host.h"

#include "stdio.h"

#ifdef STATIC_PMD_SLICES
    #define PGD_EPTR    ((VMM_PGD_BPTR))    // PGD is not mapped in this mode.
#else
    #define PGD_EPTR    ((VMM_PGD_BPTR) + PTRS_PER_PGD)
#endif
#define PMD_BPTR    ((PGD_EPTR))
#ifdef STATIC_PMD_SLICES
    #define PMD_EPTR    ((PMD_BPTR) + N_STATIC_PMD_SLICES*PTRS_PER_PMD)
#else
    #define PMD_EPTR    ((PMD_BPTR) + PTRS_PER_PMD)
#endif
#define PTE_BPTR    ((PMD_EPTR))
#define PTE_EPTR    ((PTE_BPTR) + PTRS_PER_PTE)

#ifdef PTW_MEAS_PERF_FINE
    #define PTW_MEAS_PERF
#endif
#ifdef PTW_MEAS_PERF
    #define MEAS_PERF
#endif

#ifndef LOG_LVL_PTW
    #define LOG_LVL_PTW RT_LOG_ERROR
#endif

/**
 * Get physical address of PMD through PGD index.
 *
 * @param   pgd_index       Index to the PGD.
 * @param   pmd_phys_addr   Pointer through which the physical address of the PMD shall be returned.
 *
 * @return  0 on success (in this case, `pmd_phys_addr` contains the physical address of the PMD
 *          after this function returns); negative value with an errno on errors (in this case, the
 *          value of `pmd_phys_addr` is undefined after this function returns).
 */
static inline int get_pmd_phys_addr(const unsigned pgd_index, phys_addr_t* const pmd_phys_addr)
{
    int ret = 0;

    #ifdef PTW_MEAS_PERF_FINE
        perf_cycles_push();
    #endif

    const phys_addr_t* const pgd_ptr = VMM_PGD_BPTR + pgd_index;
    ret = copy_phys_addr(pmd_phys_addr, pgd_ptr);
    if (ret < 0)
        return ret;

    #ifdef PTW_MEAS_PERF_FINE
        perf_cycles_push();
    #endif

    ret = pgd_val_is_pmd_addr(pmd_phys_addr);
    if (ret != 1)
        return ret;

    #ifdef PTW_MEAS_PERF_FINE
        perf_cycles_push();
    #endif

    pmd_phys_addr->lower = pmd_phys_addr->lower & PAGE_MASK;

    return 0;
}

/**
 * Get physical address of PTE through PMD index.
 *
 * @param   pmd_index       Index to the PMD.
 * @param   pte_phys_addr   Pointer through which the physical address of the PTE shall be returned.
 *
 * @return  0 on success (in this case, `pte_phys_addr` contains the physical address of the PTE
 *          after this function returns); negative value with an errno on errors (in this case, the
 *          value of `pte_phys_addr` is undefined after this function returns).
 */
static inline int get_pte_phys_addr(const unsigned pmd_index, phys_addr_t* const pte_phys_addr)
{
    int ret = 0;

    #ifdef PTW_MEAS_PERF_FINE
        perf_cycles_push();
    #endif

    const phys_addr_t* const pmd_ptr = PMD_BPTR + pmd_index;
    ret = copy_phys_addr(pte_phys_addr, pmd_ptr);
    if (ret < 0)
        return ret;

    #ifdef PTW_MEAS_PERF_FINE
        perf_cycles_push();
    #endif

    ret = pmd_val_is_pte_addr(pte_phys_addr);
    if (ret != 1)
        return ret;

    #ifdef PTW_MEAS_PERF_FINE
        perf_cycles_push();
    #endif

    pte_phys_addr->lower = pte_phys_addr->lower & PAGE_MASK;

    return 0;
}

/**
 * Get physical address of page through PTE index.
 *
 * @param   pte_index       Index to the PTE.
 * @param   page_phys_addr  Pointer through which the physical address of the page shall be
 *                          returned.
 * @param   page_rdonly     Pointer to a byte that shall be set to `1` if the page is read-only.
 *
 * @return  0 on success (in this case, the output parameters are set to valid values as described
 *          above); negative value with an errno on errors (in this case, the value of the output
 *          parameters is undefined).
 */
static inline int get_page_phys_addr(const unsigned pte_index, phys_addr_t* const page_phys_addr,
        unsigned char* const page_rdonly)
{
    int ret = 0;

    const phys_addr_t* const pte_ptr = PTE_BPTR + pte_index;
    ret = copy_phys_addr(page_phys_addr, pte_ptr);
    if (ret < 0)
        return ret;

    ret = pte_val_is_valid_page_addr(page_phys_addr);
    if (ret != 1)
        return ret;

    ret = pte_val_is_rdonly_page(page_phys_addr);
    if (ret < 0)
        return ret;
    *page_rdonly = ret;

    page_phys_addr->lower = page_phys_addr->lower & PAGE_MASK;

    return 0;
}

#ifndef STATIC_PMD_SLICES
static inline int config_pmd_rab_slice(const phys_addr_t* const pmd_phys_addr)
{
    return config_rab_slice((virt_addr_t)PMD_BPTR, (virt_addr_t)PMD_EPTR, pmd_phys_addr,
            RAB_CFG_PMD_PTR, 1, 1);
}
#endif

static inline int config_pte_rab_slice(const phys_addr_t* const pte_phys_addr)
{
    return config_rab_slice((virt_addr_t)PTE_BPTR, (virt_addr_t)PTE_EPTR, pte_phys_addr,
            RAB_CFG_PTE_PTR, 1, 1);
}

// As no PTE is mapped at startup, initialize this variable to a value that cannot be a PTE address.
static virt_addr_t cur_mapped_pte_addr = 0xFFFFFFFF;

int virt_addr_to_page_phys_addr(const virt_addr_t virt_addr,
        phys_addr_t* const page_phys_addr, unsigned char* const page_rdonly)
{
    int ret = 0;

    const virt_addr_t pte_addr = virt_addr & PMD_MASK;
    if (pte_addr != cur_mapped_pte_addr) {

        #ifndef STATIC_PMD_SLICES

            #ifdef PTW_MEAS_PERF
                perf_cycles_push();
            #endif

            phys_addr_t pmd_phys_addr;
            ret = get_pmd_phys_addr(pgd_index(virt_addr), &pmd_phys_addr);
            if (ret < 0) {
                #if RT_LOG_ERRORS(LOG_LVL_PTW)
                    rt_error("Failed to read PGD[%u] with errno %d!\n", pgd_index(virt_addr), -ret);
                #endif
                return ret;
            }

            #if RT_LOG_DEBUGS(LOG_LVL_PTW)
            {
                const size_t buf_size = sizeof(char) * PHYS_ADDR_STRLEN;
                char* const buf = rt_alloc(RT_ALLOC_CL_DATA, buf_size);
                if (buf != NULL) {
                    sprint_phys_addr(buf, &pmd_phys_addr);
                    rt_debug("Read PGD[%u], got PMD PA %s.\n", pgd_index(virt_addr), buf);
                    rt_free(RT_ALLOC_CL_DATA, buf, buf_size);
                }
            }
            #endif

            #ifdef PTW_MEAS_PERF
                perf_cycles_push();
            #endif

            ret = config_pmd_rab_slice(&pmd_phys_addr);
            if (ret < 0) {
                #if RT_LOG_ERRORS(LOG_LVL_PTW)
                    rt_error("Failed to setup RAB slice for PMD with errno %d!\n", -ret);
                #endif
                return ret;
            }

        #endif

        #ifdef PTW_MEAS_PERF
            perf_cycles_push();
        #endif

        phys_addr_t pte_phys_addr;
        ret = get_pte_phys_addr(pmd_index(virt_addr), &pte_phys_addr);
        if (ret < 0) {
            #if RT_LOG_ERRORS(LOG_LVL_PTW)
                rt_error("Failed to read PMD[%u] with errno %d!\n", pmd_index(virt_addr), -ret);
            #endif
            return ret;
        }

        #if RT_LOG_DEBUGS(LOG_LVL_PTW)
        {
            const size_t buf_size = sizeof(char) * PHYS_ADDR_STRLEN;
            char* const buf = rt_alloc(RT_ALLOC_CL_DATA, buf_size);
            if (buf != NULL) {
                sprint_phys_addr(buf, &pte_phys_addr);
                rt_debug("Read PMD[%u], got PTE PA %s.\n", pmd_index(virt_addr), buf);
                rt_free(RT_ALLOC_CL_DATA, buf, buf_size);
            }
        }
        #endif

        #ifdef PTW_MEAS_PERF
            perf_cycles_push();
        #endif

        ret = config_pte_rab_slice(&pte_phys_addr);
        if (ret < 0) {
            #if RT_LOG_ERRORS(LOG_LVL_PTW)
                rt_error("Failed to setup RAB slice for PTE with errno %d!\n", -ret);
            #endif
            return ret;
        }

        #ifdef PTW_MEAS_PERF
            perf_cycles_push();
        #endif

        cur_mapped_pte_addr = pte_addr;

    }
    #ifdef PTW_MEAS_PERF
        else {
            #ifndef STATIC_PMD_SLICES
                perf_cycles_push();
                // get_pmd_phys_addr()
                #ifdef PTW_MEAS_PERF_FINE
                    perf_cycles_push();
                    perf_cycles_push();
                    perf_cycles_push();
                #endif
                perf_cycles_push();
            #endif
            perf_cycles_push();
            // get_pte_phys_addr()
            #ifdef PTW_MEAS_PERF_FINE
                perf_cycles_push();
                perf_cycles_push();
                perf_cycles_push();
            #endif
            perf_cycles_push();
            perf_cycles_push();
        }
    #endif

    ret = get_page_phys_addr(pte_index(virt_addr), page_phys_addr, page_rdonly);
    if (ret < 0) {
        #if RT_LOG_ERRORS(LOG_LVL_PTW)
            rt_error("Failed to read PTE[%u] with errno %d!\n", pte_index(virt_addr), -ret);
        #endif
        return ret;
    }

    #if RT_LOG_DEBUGS(LOG_LVL_PTW)
    {
        const size_t buf_size = sizeof(char) * PHYS_ADDR_STRLEN;
        char* const buf = rt_alloc(RT_ALLOC_CL_DATA, buf_size);
        if (buf != NULL) {
            sprint_phys_addr(buf, &page_phys_addr);
            rt_debug("Read PTE[%u], got page PA %s.\n", pte_index(virt_addr), buf);
            rt_free(RT_ALLOC_CL_DATA, buf, buf_size);
        }
    }
    #endif

    #ifdef PTW_MEAS_PERF
        perf_cycles_push();
    #endif

    return 0;
}
