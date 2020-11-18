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

#include "vmm/vmm.h"

#include "archi-host/pgtable_hwdef.h"
#include "archi-host/phys_addr.h"
#include "archi-host/virt_addr.h"
#include "hal/utils.h"                  // BIT_MASK_ONE()
#include "hal/rab/rab_v1.h"
#include "pulp.h"
#include "rt/rt_alloc.h"                // rt_alloc(), rt_free()
#include "rt/rt_debug.h"
#include "vmm/config.h"
#include "vmm/host.h"

#include <stdio.h>
#include <errno.h>

#define RAB_CFG_VMM_BPTR        ((rab_cfg_t*)(RAB_CFG_PTE_PTR + 1))
#define RAB_CFG_VMM_N_SLICES    ((unsigned)(RAB_CFG_EPTR - RAB_CFG_VMM_BPTR))

__attribute__((section(".heapsram")))
static rab_cfg_t* page_rab_cfg_ptr = RAB_CFG_VMM_BPTR;

typedef struct mht_t {
    int core_id;
    int cluster_id;
} mht_t;

#if (VMM_RAB_LVL == 2)
    __attribute__((section(".heapsram")))
    static unsigned char page_rab_cfg_l2_i_set[RAB_L2_N_SETS] = {0};
#endif

static inline void reset_page_rab_cfg_ptrs()
{
    page_rab_cfg_ptr = RAB_CFG_VMM_BPTR;

    #if (VMM_RAB_LVL == 2)
        for (unsigned i=0; i<RAB_L2_N_SETS; i++) {
            page_rab_cfg_l2_i_set[i] = 0;
        }
    #endif
}

static inline int config_page_rab_entry(const virt_addr_t page_virt_addr,
        const phys_addr_t* const page_phys_addr, const unsigned char page_rdonly,
        const unsigned char cache_coherent)
{
    #if (VMM_RAB_LVL == 1)
        // RAB slices are being replaced through the FIFO algorithm.
        if (page_rab_cfg_ptr >= RAB_CFG_EPTR)
            page_rab_cfg_ptr = RAB_CFG_VMM_BPTR;

        return config_rab_slice(page_virt_addr, page_virt_addr + PAGE_SIZE, page_phys_addr,
                page_rab_cfg_ptr++, page_rdonly, cache_coherent);
    #else // VMM_RAB_LVL == 2
        const virt_pfn_t virt_pfn = virt_addr2pfn(page_virt_addr);
        const phys_pfn_t phys_pfn = phys_addr2pfn(page_phys_addr);

        const rab_l2_set_t l2_set = page_set(virt_pfn);

        // RAB L2 entries are being replaced through the FIFO algorithm on a set basis.
        if (page_rab_cfg_l2_i_set[l2_set] >= RAB_L2_N_ENTRIES_PER_SET)
            page_rab_cfg_l2_i_set[l2_set] = 0;

        return config_rab_l2_entry(virt_pfn, phys_pfn, l2_set,
                page_rab_cfg_l2_i_set[l2_set]++, page_rdonly, cache_coherent);
    #endif
}

int map_page(const void* const virt_ptr)
{
    int ret = 0;

    const virt_addr_t virt_addr = (virt_addr_t)virt_ptr;

    phys_addr_t     page_phys_addr;
    unsigned char   page_rdonly;
    ret = virt_addr_to_page_phys_addr(virt_addr, &page_phys_addr, &page_rdonly);
    if (ret != 0) {
        #if RT_LOG_ERRORS(LOG_LVL_VMM)
        {
            const size_t buf_size = sizeof(char) * VIRT_ADDR_STRLEN;
            char* const buf = rt_alloc(RT_ALLOC_CL_DATA, buf_size);
            if (buf != NULL) {
                sprint_virt_addr(buf, &virt_addr);
                rt_error("Failed to find the page physical address for VA %s with errno %d!\n",
                        buf, -ret);
                rt_free(RT_ALLOC_CL_DATA, buf, buf_size);
            }
        }
        #endif
        #if RT_LOG_DEBUGS(LOG_LVL_VMM)
            print_rab_cfg(RAB_CFG_VMM_BPTR, RAB_CFG_EPTR, 1);
        #endif
        return ret;
    }

    const virt_addr_t page_virt_addr = page_addr((unsigned)virt_addr);
    ret = config_page_rab_entry(page_virt_addr, &page_phys_addr, page_rdonly, 1);
    if (ret != 0) {
        #if RT_LOG_ERRORS(LOG_LVL_VMM)
        {
            const size_t va_buf_size = sizeof(char) * VIRT_ADDR_STRLEN;
            char* const va_buf = rt_alloc(RT_ALLOC_CL_DATA, va_buf_size);
            if (va_buf != NULL) {
                sprint_virt_addr(va_buf, &page_virt_addr);
                const size_t pa_buf_size = sizeof(char) * PHYS_ADDR_STRLEN;
                char* const pa_buf = rt_alloc(RT_ALLOC_CL_DATA, pa_buf_size);
                if (pa_buf != NULL) {
                    sprint_phys_addr(pa_buf, &page_phys_addr);
                    rt_error("Failed to configure RAB entry for page with VA %s, PA %s "
                            "with errno %d!\n", va_buf, pa_buf, -ret);
                    rt_free(RT_ALLOC_CL_DATA, pa_buf, pa_buf_size);
                }
                rt_free(RT_ALLOC_CL_DATA, va_buf, va_buf_size);
            }
        }
        #endif
        return ret;
    }

    #if VMM_RAB_LVL == 1
        #if RT_LOG_TRACES(LOG_LVL_VMM)
            rt_trace("RAB configuration after mapping page:\n");
            print_rab_cfg(RAB_CFG_BPTR, RAB_CFG_EPTR, 1);
        #endif
    #endif

    return 0;
}

int map_pages(const void* const virt_ptr, const size_t n_bytes)
{
    const virt_addr_t end_addr = (virt_addr_t)virt_ptr + n_bytes;
    const virt_addr_t first_page = page_addr((virt_addr_t)virt_ptr);
    const virt_addr_t last_page = page_addr(end_addr - 1);

    // Make sure that the requested number of pages can be simultaneously mapped by RAB.
    const unsigned n_pages = ((last_page - first_page) >> PAGE_SHIFT) + 1;
    if (n_pages > RAB_CFG_VMM_N_SLICES) {
        #if RT_LOG_ERRORS(LOG_LVL_VMM)
            rt_error("Failed to map %d pages because RAB can hold at most %d slices!\n",
                    n_pages, RAB_CFG_VMM_N_SLICES);
        #endif
        return -ENOMEM;
    }

    for (virt_addr_t page_addr = first_page; page_addr <= last_page; page_addr += PAGE_SIZE) {
        const int ret = map_page((void*)page_addr);
        if (ret < 0) {
            #if RT_LOG_ERRORS(LOG_LVL_VMM)
            {
                const size_t buf_size = sizeof(char) * VIRT_ADDR_STRLEN;
                char* const buf = rt_alloc(RT_ALLOC_CL_DATA, buf_size);
                if (buf != NULL) {
                    sprint_virt_addr(buf, &page_addr);
                    rt_error("Failed to map page for VA %s with errno %d!\n", buf, -ret);
                    rt_free(RT_ALLOC_CL_DATA, buf, buf_size);
                }
            }
            #endif
            return ret;
        }
    }

    #if RT_LOG_DEBUGS(LOG_LVL_VMM)
        rt_debug("Successfully mapped %d pages into RAB.\n", n_pages);
        print_rab_cfg(RAB_CFG_BPTR, RAB_CFG_EPTR, 1);
    #endif

    return 0;
}

/**
 * Recently Mapped Pages
 *
 * This is a list of base addresses of pages that were mapped recently.  List entries with a value
 * of zero are invalid (the zero page is not accessible in Linux).
 */
__attribute__((section(".heapsram")))
static virt_addr_t recently_mapped_pages[ARCHI_NB_PE] = {0};
virt_addr_t* const rmp_eptr = recently_mapped_pages + ARCHI_NB_PE;
virt_addr_t*       rmp_wptr = recently_mapped_pages;

static inline void reset_recently_mapped_pages()
{
    for (unsigned i=0; i<ARCHI_NB_PE; i++) {
        recently_mapped_pages[i] = 0;
    }
    rmp_wptr = recently_mapped_pages;
}

static inline unsigned page_has_recently_been_mapped(const virt_addr_t page_addr)
{
    for (const virt_addr_t* rmp_rptr = recently_mapped_pages; rmp_rptr < rmp_eptr; ++rmp_rptr) {
        if (*rmp_rptr == page_addr && *rmp_rptr != 0)
            return 1;
    }
    return 0;
}

static inline void add_to_recently_mapped_pages(const virt_addr_t page_addr)
{
    *rmp_wptr = page_addr;

    if (++rmp_wptr >= rmp_eptr)
        rmp_wptr = recently_mapped_pages;
}

static inline void remove_from_recently_mapped_pages(const virt_addr_t page_addr)
{
    for (virt_addr_t* rmp_wptr = recently_mapped_pages; rmp_wptr < rmp_eptr; ++rmp_wptr) {
        if (*rmp_wptr == page_addr)
            *rmp_wptr = 0;
    }
}

static inline unsigned page_is_mapped(const virt_addr_t page_addr)
{
    return !pulp_tryread_prefetch((const unsigned int* const)page_addr);
}

int unmap_page(const void* const virt_ptr)
{
    int ret = 0;

    const virt_addr_t virt_addr = (virt_addr_t)virt_ptr;

    for (rab_cfg_t* slice = RAB_CFG_VMM_BPTR; slice < RAB_CFG_EPTR; ++slice) {

        rab_cfg_val_t val;
        ret = read_rab_cfg_val(&val, slice);
        if (ret != 0) {
            #if RT_LOG_ERRORS(LOG_LVL_VMM)
                rt_error("Failed to read RAB slice with errno %d!\n", -ret);
            #endif
            return ret;
        }

        if (rab_slice_is_enabled(&val) && rab_slice_contains_virt_addr(&val, virt_addr)) {
            ret = disable_rab_slice(slice);
            if (ret != 0) {
                #if RT_LOG_ERRORS(LOG_LVL_VMM)
                    rt_error("Failed to disable RAB slice with errno %d!\n", -ret);
                #endif
                return ret;
            }
            remove_from_recently_mapped_pages(page_addr(virt_addr));
            /**
             * There may always be only one slice for each virtual address range.  At this point,
             * this slice has been found and disabled; this function has thus completed its task.
             */
            return 0;
        }

    }

    // No RAB slice that contains the virtual address has been found.
    return -ENOENT;
}

static inline int wake_up_core(const int cluster_id, const int core_id)
{
    unsigned int wake_up_addr;
    const unsigned int core_mask = BIT_MASK_ONE(core_id);
    if (cluster_id == get_cluster_id()) // wake up through demux
        wake_up_addr = eu_evt_trig_addr(ARCHI_EVT_RAB_WAKEUP);
    else    // wake up through peripheral interconnect
        wake_up_addr = eu_evt_trig_cluster_addr(cluster_id, ARCHI_EVT_RAB_WAKEUP);

    // Wake up core by setting the corresponding bit in the wake-up register.
    eu_evt_trig(wake_up_addr, core_mask);

    return 0;
}

int handle_rab_misses()
{
    int ret = 0;
    unsigned n_misses_handled = 0;

    mht_t mht;
    mht.cluster_id = get_cluster_id();
    mht.core_id    = get_core_id();

    while (1) {

        rab_miss_t rab_miss;
        ret = get_rab_miss(&rab_miss);
        if (ret != 0) {
            switch (ret) {
                case -ENOENT:
                    if (n_misses_handled > 0)
                        return 0;
                    break;
                default:
                    #if RT_LOG_ERRORS(LOG_LVL_VMM)
                        rt_error("Failed to get RAB miss with errno %d!\n", -ret);
                    #endif
                    break;  // required in case the `printf()` above is removed by the preprocessor
            }
            return ret;
        }

        if (rab_miss.intra_cluster_id != 0x2) {
            #if RT_LOG_ERRORS(LOG_LVL_VMM)
            {
                const size_t buf_size = sizeof(char) * VIRT_ADDR_STRLEN;
                char* const buf = rt_alloc(RT_ALLOC_CL_DATA, buf_size);
                if (buf != NULL) {
                    sprint_virt_addr(buf, &(rab_miss.virt_addr));
                    rt_error("Can only handle RAB misses from cores! Will not map VA %s "
                            "for ID 0x%X!\n", buf,
                            (rab_miss.intra_cluster_id << AXI_ID_WIDTH_CORE) | rab_miss.core_id);
                    rt_free(RT_ALLOC_CL_DATA, buf, buf_size);
                }
            }
            #endif
            return -EFAULT;
        } else if ( (rab_miss.cluster_id == mht.cluster_id) && (rab_miss.core_id == mht.core_id) ) {
            #if RT_LOG_INFOS(LOG_LVL_VMM)
                rt_info("Skipping RAB miss produced by MHT.\n");
            #endif
            continue;
        } else {
            #if RT_LOG_INFOS(LOG_LVL_VMM)
            {
                const size_t buf_size = sizeof(char) * VIRT_ADDR_STRLEN;
                char* const buf = rt_alloc(RT_ALLOC_CL_DATA, buf_size);
                if (buf != NULL) {
                    sprint_virt_addr(buf, &(rab_miss.virt_addr));
                    rt_info("Handling miss by core (%u,%u) at VA %s.\n",
                            rab_miss.cluster_id, rab_miss.core_id, buf);
                    rt_free(RT_ALLOC_CL_DATA, buf, buf_size);
                }
            }
            #endif

            const virt_addr_t miss_page = page_addr(rab_miss.virt_addr);
            if ( !page_has_recently_been_mapped(miss_page) && !page_is_mapped(miss_page) ) {
                ret = map_page((void*)(miss_page));
                if (ret < 0) {
                    #if RT_LOG_ERRORS(LOG_LVL_VMM)
                    {
                        const size_t buf_size = sizeof(char) * VIRT_ADDR_STRLEN;
                        char* const buf = rt_alloc(RT_ALLOC_CL_DATA, buf_size);
                        if (buf != NULL) {
                            sprint_virt_addr(buf, &(rab_miss.virt_addr));
                            rt_error("Failed to map page for VA %s for core (%u,%u) "
                                    "with errno %d!\n", buf, rab_miss.cluster_id, rab_miss.core_id,
                                    -ret);
                            rt_free(RT_ALLOC_CL_DATA, buf, buf_size);
                        }
                    }
                    #endif
                    return ret;
                } else {
                    add_to_recently_mapped_pages(miss_page);
                    #if RT_LOG_DEBUGS(LOG_LVL_VMM)
                    {
                        const size_t buf_size = sizeof(char) * VIRT_ADDR_STRLEN;
                        char* const buf = rt_alloc(RT_ALLOC_CL_DATA, buf_size);
                        if (buf != NULL) {
                            sprint_virt_addr(buf, &miss_page);
                            rt_debug("Page at VA %s mapped successfully.\n", buf);
                            rt_free(RT_ALLOC_CL_DATA, buf, buf_size);
                        }
                    }
                    #endif
                }
            } else {
                #if RT_LOG_DEBUGS(LOG_LVL_VMM)
                {
                    const size_t buf_size = sizeof(char) * VIRT_ADDR_STRLEN;
                    char* const buf = rt_alloc(RT_ALLOC_CL_DATA, buf_size);
                    if (buf != NULL) {
                        sprint_virt_addr(buf, &miss_page);
                        rt_debug("Did not map page for VA %s because it has been mapped recently.\n",
                                buf);
                        rt_free(RT_ALLOC_CL_DATA, buf, buf_size);
                    }
                }
                #endif
            }

            if (!rab_miss.is_prefetch) {
                ret = wake_up_core(rab_miss.cluster_id, rab_miss.core_id);
                if (ret < 0) {
                    #if RT_LOG_ERRORS(LOG_LVL_VMM)
                        rt_error("Failed to wake up core (%u,%u) with errno %d!\n",
                                rab_miss.cluster_id, rab_miss.core_id, -ret);
                    #endif
                    return ret;
                }
                //#if RT_LOG_TRACES(LOG_LVL_VMM)
                //    rt_trace("Woke up core (%u,%u).\n", rab_miss.cluster_id, rab_miss.core_id);
                //#endif
            } else {
                #if RT_LOG_DEBUGS(LOG_LVL_VMM)
                    rt_debug("Did not wake up core due to prefetch.\n");
                #endif
            }

            ++n_misses_handled;
        }
    }
}

void reset_vmm()
{
    reset_recently_mapped_pages();

    reset_page_rab_cfg_ptrs();
}
