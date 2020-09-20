/*
 * This file is part of the PULP device driver.
 *
 * Copyright (C) 2018 ETH Zurich, University of Bologna
 *
 * Authors: Pirmin Vogel <vogelpi@iis.ee.ethz.ch>
 *          Andreas Kurth <akurth@iis.ee.ethz.ch>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include <linux/version.h>

#include "pulp_rab.h"
#include "pulp_mem.h" /* for cache invalidation */
#include "pulp_profile.h"

#undef ARM
#include "archi/pulp.h"

// global variables {{{
static L1Tlb l1;
static L2Tlb l2;
static PulpDev *pulp;

// striping information
static RabStripeReq rab_stripe_req[RAB_L1_N_MAPPINGS_PORT_1];

// miss handling routine
static char rab_mh_wq_name[10] = "RAB_MH_WQ";
static struct workqueue_struct *rab_mh_wq = 0;
static struct work_struct rab_mh_w;
static struct task_struct *user_task;
static struct mm_struct *user_mm;
static unsigned rab_mh_addr[RAB_MH_FIFO_DEPTH];
static unsigned rab_mh_meta[RAB_MH_FIFO_DEPTH];
static unsigned rab_mh;
static unsigned rab_mh_date;
static unsigned rab_mh_acp;
static unsigned rab_mh_lvl;
static unsigned rab_soc_mh_is_ena;
static unsigned rab_n_slices_reserved_for_host;

// AX logger
#if RAB_AX_LOG_EN == 1
static unsigned *rab_ar_log_buf;
static unsigned *rab_aw_log_buf;
static unsigned *rab_cfg_log_buf;
static unsigned rab_ar_log_buf_idx = 0;
static unsigned rab_aw_log_buf_idx = 0;
static unsigned rab_cfg_log_buf_idx = 0;
#endif

// for profiling
#if defined(PROFILE_RAB_STR) || defined(PROFILE_RAB_MH)
static unsigned host_clk_cntr_value = 0;
static unsigned host_clk_cntr_value_start = 0;

static unsigned n_cyc_response = 0; // per update request
static unsigned n_cyc_update = 0; // per update request
static unsigned n_cyc_setup = 0; // per stripe request (multiple elements, pages)
static unsigned n_cyc_cache_flush = 0; // per striped element
static unsigned n_cyc_get_user_pages = 0; // per striped element

static unsigned *n_cyc_buf_response;
static unsigned *n_cyc_buf_update;
static unsigned *n_cyc_buf_setup;
static unsigned *n_cyc_buf_cache_flush;
static unsigned *n_cyc_buf_get_user_pages;

static unsigned idx_buf_response;
static unsigned idx_buf_update;
static unsigned idx_buf_setup;
static unsigned idx_buf_cache_flush;
static unsigned idx_buf_get_user_pages;

static unsigned n_cyc_tot_response;
static unsigned n_cyc_tot_update;
static unsigned n_cyc_tot_setup;
static unsigned n_cyc_tot_cache_flush;
static unsigned n_cyc_tot_get_user_pages;

  #ifdef PROFILE_RAB_STR
static unsigned n_cyc_cleanup = 0; // per stripe free    (multiple elements, pages)
static unsigned n_cyc_map_sg = 0; // per striped element

static unsigned *n_cyc_buf_cleanup;
static unsigned *n_cyc_buf_map_sg;

static unsigned idx_buf_cleanup;
static unsigned idx_buf_map_sg;

static unsigned n_cyc_tot_cleanup;
static unsigned n_cyc_tot_map_sg;

static unsigned n_pages_setup;
static unsigned n_cleanups;
static unsigned n_slices_updated;
static unsigned n_updates;
  #endif

  #ifdef PROFILE_RAB_MH
static unsigned n_cyc_response_tmp;

static unsigned n_cyc_schedule = 0; // per miss

static unsigned *n_cyc_buf_schedule;

static unsigned idx_buf_schedule;

static unsigned n_cyc_tot_schedule;

static unsigned n_first_misses = 0;
static unsigned n_misses = 0;
  #endif
#endif

#ifdef PROFILE_RAB_MH_SIMPLE
static unsigned n_first_misses = 0;
static unsigned n_misses = 0;
static unsigned n_schedule = 0;
#endif

// }}}

// functions

// setup {{{
int pulp_rab_setup(PulpDev *pulp)
{
  int err;

  // setup default fixed driver mappings
  RabSliceReq req;
  req.flags_drv = RAB_FLAGS_DRV_FIXED | RAB_FLAGS_DRV_CONST;
  req.flags_hw = RAB_FLAGS_HW_EN | RAB_FLAGS_HW_READ | RAB_FLAGS_HW_WRITE;
  req.rab_lvl = 0;
  req.rab_mapping = 0;
  req.date_exp = RAB_MAX_DATE;
  req.date_cur = RAB_MAX_DATE;

  // Port 0: Host -> PULP
  req.rab_port = 0;
  // L2
  req.addr_start = L2_MEM_H_BASE_ADDR;
  req.addr_end = req.addr_start + L2_MEM_SIZE_B;
  err = pulp_rab_req(pulp->rab_config, &req);
  if (err)
    return err;

  // mbox
  req.addr_start = MBOX_H_BASE_ADDR;
  req.addr_end = req.addr_start + MBOX_SIZE_B;
  err = pulp_rab_req(pulp->rab_config, &req);
  if (err)
    return err;

  // Cluster (L1 and peripherals)
  req.addr_start = PULP_H_BASE_ADDR;
  req.addr_end = req.addr_start + CLUSTERS_SIZE_B;
  err = pulp_rab_req(pulp->rab_config, &req);
  if (err)
    return err;

  // Port 1: PULP -> Host
  // L3
  req.rab_port = 1;
  req.addr_start = L3_MEM_BASE_ADDR;
  req.addr_end = req.addr_start + L3_MEM_SIZE_B;
  err = pulp_rab_req(pulp->rab_config, &req);
  if (err)
    return err;

#if PLATFORM == ARIANE
  // HACK: setup access to RAB via host
  req.rab_port = 1;
  req.addr_start = ARCHI_RAB_CFG_ADDR;
  req.addr_end = req.addr_start + RAB_CONFIG_SIZE_B;
  req.addr_offset = RAB_CONFIG_BASE_ADDR;
  err = pulp_rab_req(pulp->rab_config, &req);
  if (err)
    return err;
#endif

  return 0;
}

//}}}

// init {{{
int pulp_rab_init(PulpDev *pulp_ptr)
{
  int err = 0;

  // initialize the pointer for pulp_rab_update/switch
  pulp = pulp_ptr;

  // initialize management structures and L2 hardware
  pulp_rab_l1_init();
#if PLATFORM != ZEDBOARD
  pulp_rab_l2_init(pulp->rab_config);
#endif

  // initialize miss handling control
  rab_mh = 0;
  rab_mh_date = 0;
  rab_mh_acp = 0;
  rab_mh_lvl = 0;
  rab_n_slices_reserved_for_host = RAB_L1_N_SLICES_PORT_1;

  // prepare the default mappings
  err = pulp_rab_setup(pulp);
  if (err)
    return err;

  // by default, the SoC does not handle RAB misses.
  pulp_rab_soc_mh_dis(pulp->rab_config);

// initialize AX logger
#if RAB_AX_LOG_EN == 1
  err = pulp_rab_ax_log_init();
  if (err)
    return err;
#endif

#ifdef PROFILE_RAB_MH_SIMPLE
  n_first_misses = 0;
  n_misses = 0;
  n_schedule = 0;
#endif

// prepare for profiling
#if defined(PROFILE_RAB_STR) || defined(PROFILE_RAB_MH)
  err = pulp_rab_prof_init();
  if (err)
    return err;
#endif

  return err;
}
// }}}

// release {{{
int pulp_rab_release(bool driver)
{
  unsigned i, offset;
  int ret = 0;

  const unsigned rab_n_slices_host = rab_n_slices_reserved_for_host;

  if (DEBUG_LEVEL_RAB > 0) {
    printk(KERN_INFO "PULP - RAB: Start release.\n");
  }

  /* Disable the SoC RAB miss handler.
   *
   * This also disables the RAB slices mapping the initital levels of the page
   * table.
   */
  ret = pulp_rab_soc_mh_dis(pulp->rab_config);
  if (ret != 0 && ret != -EALREADY) {
    printk(KERN_WARNING "PULP - RAB: Failed to disable SoC RAB Miss Handler!\n");
    return ret;
  }

  // disable the host RAB miss handler
  pulp_rab_mh_dis();

  // free RAB slices (L1 TLB) managed by SoC
  for (i = rab_n_slices_host; i < RAB_L1_N_SLICES_PORT_1; i++) {
    offset = 0x20 * (RAB_L1_N_SLICES_PORT_0 + i);
    iowrite32(0, (void *)((unsigned long)pulp->rab_config + offset + 0x38));
  }

  /* Free RAB entries managed by host and SoC and reset driver management
   * structures.
   *
   * L1-striped mappings and statically allocated mappings/mappings created
   * by the host miss handler are freed separately through the _free and
   * _free_striped functions, respectively.
   *
   * Mappings in the L2 TLB created both by the host and the SoC are freed
   * through a call to the pulp_rab_free function.
   */
  for (i = 0; i < RAB_L1_N_MAPPINGS_PORT_1; i++) {
    pulp_rab_free_striped(pulp->rab_config, i);
  }
  pulp_rab_free(pulp->rab_config, RAB_MAX_DATE - 1, driver);

#ifdef PROFILE_RAB_MH_SIMPLE
  printk(KERN_INFO "PROFILE_RAB_MH_SIMPLE: n_misses = %d, n_first_misses = %d, n_schedule = %d\n", n_misses, n_first_misses,
         n_schedule);

  n_first_misses = 0;
  n_misses = 0;
  n_schedule = 0;
#endif

  return 0;
}
// }}}

// L1 Management {{{
/***********************************************************************************
 *
 * ██╗     ██╗    ███╗   ███╗ ██████╗ ███╗   ███╗████████╗
 * ██║    ███║    ████╗ ████║██╔════╝ ████╗ ████║╚══██╔══╝
 * ██║    ╚██║    ██╔████╔██║██║  ███╗██╔████╔██║   ██║
 * ██║     ██║    ██║╚██╔╝██║██║   ██║██║╚██╔╝██║   ██║
 * ███████╗██║    ██║ ╚═╝ ██║╚██████╔╝██║ ╚═╝ ██║   ██║
 * ╚══════╝╚═╝    ╚═╝     ╚═╝ ╚═════╝ ╚═╝     ╚═╝   ╚═╝
 *
 ***********************************************************************************/

// l1_init {{{
void pulp_rab_l1_init(void)
{
  int i, j;

  // Port 0
  for (i = 0; i < RAB_L1_N_SLICES_PORT_0; i++) {
    l1.port_0.slices[i].date_cur = 0;
    l1.port_0.slices[i].date_exp = 0;
    l1.port_0.slices[i].addr_start = 0;
    l1.port_0.slices[i].addr_end = 0;
    l1.port_0.slices[i].addr_offset = 0;
    l1.port_0.slices[i].flags_hw = 0;
  }

  // Port 1
  for (i = 0; i < RAB_L1_N_MAPPINGS_PORT_1; i++) {
    for (j = 0; j < RAB_L1_N_SLICES_PORT_1; j++) {
      l1.port_1.mappings[i].slices[j].date_cur = 0;
      l1.port_1.mappings[i].slices[j].date_exp = 0;
      l1.port_1.mappings[i].slices[j].page_ptr_idx = 0;
      l1.port_1.mappings[i].slices[j].page_idx_start = 0;
      l1.port_1.mappings[i].slices[j].page_idx_end = 0;
      l1.port_1.mappings[i].slices[j].flags_drv = 0;
      l1.port_1.mappings[i].slices[j].addr_start = 0;
      l1.port_1.mappings[i].slices[j].addr_end = 0;
      l1.port_1.mappings[i].slices[j].addr_offset = 0;
      l1.port_1.mappings[i].slices[j].flags_hw = 0;
      l1.port_1.mappings[i].page_ptrs[j] = 0;
      l1.port_1.mappings[i].page_ptr_ref_cntrs[j] = 0;
    }
  }
  l1.port_1.mapping_active = 0;

  return;
}
// }}}

// page_ptrs_get_field {{{
int pulp_rab_page_ptrs_get_field(RabSliceReq *rab_slice_req)
{
  int err, i;

  err = 0;

  // get field in page_ptrs array
  for (i = 0; i < RAB_L1_N_SLICES_PORT_1; i++) {
    if (l1.port_1.mappings[rab_slice_req->rab_mapping].page_ptr_ref_cntrs[i] == 0) {
      rab_slice_req->page_ptr_idx = i;
      break;
    }
    if (i == (RAB_L1_N_SLICES_PORT_1 - 1)) {
      printk(KERN_INFO "PULP - RAB L1: No page_ptrs field available on Port 1.\n");
      return -EIO;
    }
  }

  return err;
}
// }}}

// slice_check {{{
int pulp_rab_slice_check(RabSliceReq *rab_slice_req)
{
  int expired, fixed_i, fixed;
  unsigned char date_exp_i;

  expired = 0;
  fixed = BIT_GET(rab_slice_req->flags_drv, RAB_FLAGS_DRV_FIXED);

  if (rab_slice_req->rab_port == 0) {
    date_exp_i = l1.port_0.slices[rab_slice_req->rab_slice].date_exp;
    fixed_i = l1.port_0.slices[rab_slice_req->rab_slice].fixed;
  } else { // Port 1
    date_exp_i = l1.port_1.mappings[rab_slice_req->rab_mapping].slices[rab_slice_req->rab_slice].date_exp;
    fixed_i = l1.port_1.mappings[rab_slice_req->rab_mapping].slices[rab_slice_req->rab_slice].fixed;
  }

  if ((rab_slice_req->date_cur > date_exp_i) || // found an expired slice
      ((rab_slice_req->date_cur == 0) && (RAB_MAX_DATE_MH == date_exp_i))) // wrap around in RAB miss handling mode
    expired = 1;

  return expired && (!fixed_i || (fixed && fixed_i));
}
// }}}

// slice_get {{{
static inline unsigned pulp_rab_slice_is_managed_by_host(const RabSliceReq *const req)
{
  // All slices on port 0 are managed by the host.
  if (req->rab_port == 0)
    return 1;

  // If the RAB Miss Handler on the SoC is not enabled, all RAB slices are managed by the host.
  if (!rab_soc_mh_is_ena)
    return 1;

  // If the RAB slice is reserved for the host, then it is managed by the host.
  if (req->rab_slice < rab_n_slices_reserved_for_host)
    return 1;

  return 0;
}

int pulp_rab_slice_get(RabSliceReq *rab_slice_req)
{
  int err, i;
  unsigned n_slices;

  err = 0;

  if (rab_slice_req->rab_port == 0)
    n_slices = RAB_L1_N_SLICES_PORT_0;
  else // Port 1
    n_slices = RAB_L1_N_SLICES_PORT_1;

  // get slice number
  for (i = 0; i < n_slices; i++) {
    rab_slice_req->rab_slice = i;

    if (pulp_rab_slice_check(rab_slice_req) && pulp_rab_slice_is_managed_by_host(rab_slice_req)) {
      // Found a slice available to the host.
      break;
    } else if (i == (n_slices - 1)) {
      // No slice is available to the host.
      err = 1;
      printk(KERN_INFO "PULP RAB L1: No slice available on Port %d.\n", rab_slice_req->rab_port);
    }
  }

  return err;
}
// }}}

// slice_free {{{
void pulp_rab_slice_free(void *rab_config, RabSliceReq *rab_slice_req)
{
  int i;
  unsigned char page_ptr_idx_old, page_idx_start_old, page_idx_end_old;
  unsigned char port, flags_drv, flags_hw;
  unsigned mapping, slice, entry;
  bool freed = false;

  struct page **pages_old;

  // read default config
  port = rab_slice_req->rab_port;
  mapping = rab_slice_req->rab_mapping;
  slice = rab_slice_req->rab_slice;
  flags_drv = rab_slice_req->flags_drv;

  // fetch latest flags from driver
  entry = RAB_SLICE_BASE_OFFSET_B + RAB_SLICE_SIZE_B * (port * RAB_L1_N_SLICES_PORT_0 + slice);
  flags_hw = ioread32((void *)((unsigned long)rab_config + entry + RAB_SLICE_FLAGS_OFFSET_B));

  if (!pulp_rab_slice_is_managed_by_host(rab_slice_req)) {
    printk(KERN_WARNING "PULP - RAB: Dropping request to free slice not managed by host.\n");
    return;
  }

  // get old configuration of the selected slice
  if (port == 0) {
    page_ptr_idx_old = 0;
    pages_old = NULL;
  } else { // port 1
    page_ptr_idx_old = l1.port_1.mappings[mapping].slices[slice].page_ptr_idx;
    pages_old = l1.port_1.mappings[mapping].page_ptrs[page_ptr_idx_old];
  }

  if (pages_old) { // not used for a constant mapping, Port 0 can only hold constant mappings
    // deactivate the slice
    if (l1.port_1.mapping_active == mapping) {
      freed = true;
      iowrite32(0, (void *)((unsigned long)rab_config + entry + RAB_SLICE_FLAGS_OFFSET_B));
    }

    // determine pages to be unlocked
    page_idx_start_old = l1.port_1.mappings[mapping].slices[slice].page_idx_start;
    page_idx_end_old = l1.port_1.mappings[mapping].slices[slice].page_idx_end;

    // unlock remapped pages and invalidate caches
    if (!BIT_GET(flags_drv, RAB_FLAGS_DRV_STRIPED) && // do not unlock pages in striped mode until the last slice is freed
        !BIT_GET(flags_drv,
                 RAB_FLAGS_DRV_EVERY)) { // only unlock pages in multi-mapping rule when the last mapping is removed
      for (i = page_idx_start_old; i <= page_idx_end_old; i++) {
        if (DEBUG_LEVEL_RAB > 0) {
          printk(KERN_INFO "PULP - RAB L1: Port %d, Mapping %d, Slice %d: Unlocking Page %d.\n", port, mapping, slice, i);
        }
        // cache invalidation (in case of prefetching/speculation...)
        if (!BIT_GET(flags_hw, RAB_FLAGS_HW_CC))
          pulp_mem_cache_inv(pages_old[i], 0, PAGE_SIZE);

        // unpin user-space memory
        if (!PageReserved(pages_old[i]))
          SetPageDirty(pages_old[i]);
        put_page(pages_old[i]);
      }
    }
    // lower reference counter
    l1.port_1.mappings[mapping].page_ptr_ref_cntrs[page_ptr_idx_old]--;

    // free memory if no more references exist
    if (!l1.port_1.mappings[mapping].page_ptr_ref_cntrs[page_ptr_idx_old]) {
      if (!BIT_GET(flags_drv,
                   RAB_FLAGS_DRV_EVERY)) // only free pages ptr in multi-mapping rule when the last mapping is removed
        kfree(pages_old);
      l1.port_1.mappings[mapping].page_ptrs[page_ptr_idx_old] = 0;
    }
    if (DEBUG_LEVEL_RAB > 0) {
      printk(KERN_INFO "PULP - RAB L1: Number of references to pages pointer = %d.\n",
             l1.port_1.mappings[mapping].page_ptr_ref_cntrs[page_ptr_idx_old]);
    }
  } else if ((port == 1) && BIT_GET(flags_drv, RAB_FLAGS_DRV_CONST)) {
    if (l1.port_1.mappings[mapping].page_ptr_ref_cntrs[page_ptr_idx_old])
      l1.port_1.mappings[mapping].page_ptr_ref_cntrs[page_ptr_idx_old]--;
    if (mapping == l1.port_1.mapping_active) { // also free constant, active mappings on Port 1
      iowrite32(0, (void *)((unsigned long)rab_config + entry + RAB_SLICE_FLAGS_OFFSET_B));
      freed = true;
    }
  } else if (flags_hw != 0) {
    // clear hw flags if not matching any internal way
    iowrite32(0, (void *)((unsigned long)rab_config + entry + RAB_SLICE_FLAGS_OFFSET_B));
    freed = true;
  }

  if (freed && DEBUG_LEVEL_RAB > 0) {
    printk(KERN_INFO "PULP - RAB L1: Port %d, Mapping %d, Slice %d: Freeing.\n", port, mapping, slice);
  }

  // clear entries in management structs
  if (port == 0) {
    l1.port_0.slices[slice].date_cur = 0;
    l1.port_0.slices[slice].date_exp = 0;
    l1.port_0.slices[slice].addr_start = 0;
    l1.port_0.slices[slice].addr_end = 0;
    l1.port_0.slices[slice].addr_offset = 0;
    l1.port_0.slices[slice].flags_hw = 0;
  } else { // port 1
    l1.port_1.mappings[mapping].slices[slice].date_cur = 0;
    l1.port_1.mappings[mapping].slices[slice].date_exp = 0;
    l1.port_1.mappings[mapping].slices[slice].page_ptr_idx = 0;
    l1.port_1.mappings[mapping].slices[slice].page_idx_start = 0;
    l1.port_1.mappings[mapping].slices[slice].page_idx_end = 0;
    l1.port_1.mappings[mapping].slices[slice].flags_drv = 0;
    l1.port_1.mappings[mapping].slices[slice].addr_start = 0;
    l1.port_1.mappings[mapping].slices[slice].addr_end = 0;
    l1.port_1.mappings[mapping].slices[slice].addr_offset = 0;
    l1.port_1.mappings[mapping].slices[slice].flags_hw = 0;
  }

  return;
}
// }}}

// slice_setup {{{
int pulp_rab_slice_setup(void *rab_config, RabSliceReq *rab_slice_req, struct page **pages)
{
  unsigned offset, port, mapping, slice;
  bool fixed = false;

  port = rab_slice_req->rab_port;
  mapping = rab_slice_req->rab_mapping;
  slice = rab_slice_req->rab_slice;

  if (rab_slice_req->flags_drv & RAB_FLAGS_DRV_FIXED) {
    fixed = true;
  };

  // occupy the slice
  if (port == 0) {
    l1.port_0.slices[slice].fixed = fixed;
    l1.port_0.slices[slice].date_cur = rab_slice_req->date_cur;
    l1.port_0.slices[slice].date_exp = rab_slice_req->date_exp;

    l1.port_0.slices[slice].addr_start = rab_slice_req->addr_start;
    l1.port_0.slices[slice].addr_end = rab_slice_req->addr_end;
    l1.port_0.slices[slice].addr_offset = rab_slice_req->addr_offset;
    l1.port_0.slices[slice].flags_hw = rab_slice_req->flags_hw;
  } else { // Port 1
    l1.port_1.mappings[mapping].slices[slice].fixed = fixed;
    l1.port_1.mappings[mapping].slices[slice].date_cur = rab_slice_req->date_cur;
    l1.port_1.mappings[mapping].slices[slice].date_exp = rab_slice_req->date_exp;
    l1.port_1.mappings[mapping].slices[slice].page_ptr_idx = rab_slice_req->page_ptr_idx;
    l1.port_1.mappings[mapping].slices[slice].page_idx_start = rab_slice_req->page_idx_start;
    l1.port_1.mappings[mapping].slices[slice].page_idx_end = rab_slice_req->page_idx_end;
    l1.port_1.mappings[mapping].slices[slice].flags_drv = rab_slice_req->flags_drv;

    l1.port_1.mappings[mapping].slices[slice].addr_start = rab_slice_req->addr_start;
    l1.port_1.mappings[mapping].slices[slice].addr_end = rab_slice_req->addr_end;
    l1.port_1.mappings[mapping].slices[slice].addr_offset = rab_slice_req->addr_offset;
    l1.port_1.mappings[mapping].slices[slice].flags_hw = rab_slice_req->flags_hw;
  }

  if (port == 0) {
    // no page ptrs maintained
  } else { // Port 1

    // for the first segment, check that the selected reference list
    // entry is really free = memory has properly been freed
    if (l1.port_1.mappings[mapping].page_ptr_ref_cntrs[rab_slice_req->page_ptr_idx] & !rab_slice_req->page_idx_start &
        !BIT_GET(rab_slice_req->flags_drv, RAB_FLAGS_DRV_STRIPED)) {
      printk(KERN_WARNING "PULP - RAB L1: Selected reference list entry not free. Number of references = %d.\n",
             l1.port_1.mappings[mapping].page_ptr_ref_cntrs[rab_slice_req->page_ptr_idx]);
      return -EIO;
    }

    l1.port_1.mappings[mapping].page_ptr_ref_cntrs[rab_slice_req->page_ptr_idx]++;
    if (DEBUG_LEVEL_RAB > 0) {
      printk(KERN_INFO "PULP - RAB L1: Number of references to pages pointer = %d.\n",
             l1.port_1.mappings[mapping].page_ptr_ref_cntrs[rab_slice_req->page_ptr_idx]);
    }

    if (BIT_GET(rab_slice_req->flags_drv, RAB_FLAGS_DRV_CONST))
      l1.port_1.mappings[mapping].page_ptrs[rab_slice_req->page_ptr_idx] = 0;
    else
      l1.port_1.mappings[mapping].page_ptrs[rab_slice_req->page_ptr_idx] = pages;
  }

  if (DEBUG_LEVEL_RAB > 0)
    printk(KERN_INFO "PULP - RAB L1: Port %d, Mapping %d, Slice %d: Setting up.\n", port, mapping, slice);

  // set up new slice, configure the hardware
  if ((port == 0) || (l1.port_1.mapping_active == mapping)) {
    offset = RAB_SLICE_BASE_OFFSET_B + RAB_SLICE_SIZE_B * (port * RAB_L1_N_SLICES_PORT_0 + slice);

    iowrite32(rab_slice_req->addr_start, (void *)((unsigned long)rab_config + offset + RAB_SLICE_ADDR_START_OFFSET_B));
    iowrite32(rab_slice_req->addr_end, (void *)((unsigned long)rab_config + offset + RAB_SLICE_ADDR_END_OFFSET_B));
    IOWRITE_L(rab_slice_req->addr_offset, (void *)((unsigned long)rab_config + offset + RAB_SLICE_ADDR_OFFSET_OFFSET_B));
    iowrite32(rab_slice_req->flags_hw, (void *)((unsigned long)rab_config + offset + RAB_SLICE_FLAGS_OFFSET_B));

    if (DEBUG_LEVEL_RAB > 1) {
      printk(KERN_INFO "PULP - RAB L1: addr_start  %#x\n", rab_slice_req->addr_start);
      printk(KERN_INFO "PULP - RAB L1: addr_end    %#x\n", rab_slice_req->addr_end);
      printk(KERN_INFO "PULP - RAB L1: addr_offset %#lx\n", rab_slice_req->addr_offset);
      printk(KERN_INFO "PULP - RAB L1: flags_hw    %#x\n", rab_slice_req->flags_hw);
    }
  }

  return 0;
}
// }}}

// num_free_slices {{{
int pulp_rab_num_free_slices(RabSliceReq *rab_slice_req)
{
  int num_free_slice, i;
  unsigned n_slices;

  num_free_slice = 0;

  if (rab_slice_req->rab_port == 0)
    n_slices = RAB_L1_N_SLICES_PORT_0;
  else // Port 1
    n_slices = RAB_L1_N_SLICES_PORT_1;

  for (i = 0; i < n_slices; i++) {
    rab_slice_req->rab_slice = i;

    if (pulp_rab_slice_check(rab_slice_req)) // found an expired slice
      num_free_slice++;
  }

  return num_free_slice;
}
// }}}

// mapping_get_active {{{
int pulp_rab_mapping_get_active()
{
  return (int)l1.port_1.mapping_active;
}
// }}}

// mappping_switch {{{
void pulp_rab_mapping_switch(void *rab_config, unsigned rab_mapping)
{
  int i;
  unsigned offset;
  unsigned char prot;

  unsigned mapping_active;

  mapping_active = l1.port_1.mapping_active;

  if (DEBUG_LEVEL_RAB > 0)
    printk(KERN_INFO "PULP - RAB L1: Switch from Mapping %d to %d.\n", mapping_active, rab_mapping);

  // de-activate old mapping
  for (i = 0; i < RAB_L1_N_SLICES_PORT_1; i++) {
    RAB_GET_PROT(prot, l1.port_1.mappings[mapping_active].slices[i].flags_hw);
    if (prot) { // de-activate slices with old active config

      offset = RAB_SLICE_BASE_OFFSET_B + RAB_SLICE_SIZE_B * (1 * RAB_L1_N_SLICES_PORT_0 + i);
      iowrite32(0x0, (void *)((unsigned long)rab_config + offset + RAB_SLICE_FLAGS_OFFSET_B));

      if (DEBUG_LEVEL_RAB > 0)
        printk(KERN_INFO "PULP - RAB L1: Port %d, Mapping %d, Slice %d: Disabling.\n", 1, mapping_active, i);
    }
  }

  // set up new mapping
  for (i = 0; i < RAB_L1_N_SLICES_PORT_1; i++) {
    RAB_GET_PROT(prot, l1.port_1.mappings[rab_mapping].slices[i].flags_hw);
    if (prot & 0x1) { // activate slices with new active config
      offset = RAB_SLICE_BASE_OFFSET_B + RAB_SLICE_SIZE_B * (1 * RAB_L1_N_SLICES_PORT_0 + i);

      iowrite32(l1.port_1.mappings[rab_mapping].slices[i].addr_start,
                (void *)((unsigned long)rab_config + offset + RAB_SLICE_ADDR_START_OFFSET_B));
      iowrite32(l1.port_1.mappings[rab_mapping].slices[i].addr_end,
                (void *)((unsigned long)rab_config + offset + RAB_SLICE_ADDR_END_OFFSET_B));
      IOWRITE_L(l1.port_1.mappings[rab_mapping].slices[i].addr_offset,
                (void *)((unsigned long)rab_config + offset + RAB_SLICE_ADDR_OFFSET_OFFSET_B));
      iowrite32(l1.port_1.mappings[rab_mapping].slices[i].flags_hw,
                (void *)((unsigned long)rab_config + offset + RAB_SLICE_FLAGS_OFFSET_B));

      if (DEBUG_LEVEL_RAB > 0)
        printk(KERN_INFO "PULP - RAB L1: Port %d, Mapping %d, Slice %d: Setting up.\n", 1, rab_mapping, i);
      if (DEBUG_LEVEL_RAB > 1) {
        printk(KERN_INFO "PULP - RAB L1: addr_start  %#x\n", l1.port_1.mappings[rab_mapping].slices[i].addr_start);
        printk(KERN_INFO "PULP - RAB L1: addr_end    %#x\n", l1.port_1.mappings[rab_mapping].slices[i].addr_end);
        printk(KERN_INFO "PULP - RAB L1: addr_offset %#lx\n", l1.port_1.mappings[rab_mapping].slices[i].addr_offset);
      }
    }
  }

  l1.port_1.mapping_active = rab_mapping;

  return;
}
// }}}

// mapping_print {{{
void pulp_rab_mapping_print(void *rab_config, unsigned rab_mapping)
{
  int mapping_min, mapping_max;
  int i, j;
  unsigned offset, prot, flags_hw, n_slices, page_ptr_idx;

  if (rab_mapping == 0xFFFF) {
    mapping_min = 0;
    mapping_max = RAB_L1_N_MAPPINGS_PORT_1;
  } else if (rab_mapping == 0xAAAA) {
    mapping_min = 0;
    mapping_max = 0;
  } else {
    mapping_min = rab_mapping;
    mapping_max = rab_mapping + 1;
  }

  for (j = mapping_min; j < mapping_max; j++) {
    printk(KERN_INFO "PULP - RAB L1: Printing Mapping %d: \n", j);

    for (i = 0; i < RAB_L1_N_SLICES_PORT_1; i++) {
      RAB_GET_PROT(prot, l1.port_1.mappings[rab_mapping].slices[i].flags_hw);
      if (prot) {
        printk(KERN_INFO "Port %d, Slice %2d: %#x - %#x -> %#lx , flags_hw = %#x\n", 1, i,
               l1.port_1.mappings[j].slices[i].addr_start, l1.port_1.mappings[j].slices[i].addr_end,
               l1.port_1.mappings[j].slices[i].addr_offset, l1.port_1.mappings[j].slices[i].flags_hw);
      }
    }
  }

  if (((rab_mapping == 0xFFFF) || (rab_mapping == 0xAAAA)) && printk_ratelimit()) {
    printk(KERN_INFO "PULP - RAB L1: Printing active configuration: \n");

    for (j = 0; j < 2; j++) {
      if (j == 0) // Port 0
        n_slices = RAB_L1_N_SLICES_PORT_0;
      else // Port 1
        n_slices = RAB_L1_N_SLICES_PORT_1;

      for (i = 0; i < n_slices; i++) {
        offset = RAB_SLICE_BASE_OFFSET_B + RAB_SLICE_SIZE_B * (j * RAB_L1_N_SLICES_PORT_0 + i);

        flags_hw = ioread32((void *)((unsigned long)rab_config + offset + RAB_SLICE_FLAGS_OFFSET_B));
        RAB_GET_PROT(prot, flags_hw);
        if (prot) {
          printk(KERN_INFO "Port %d, Slice %2d: 0x%08x - 0x%08x -> 0x%010lx , flags_hw = %#x\n", j, i,
                 ioread32((void *)((unsigned long)rab_config + offset + RAB_SLICE_ADDR_START_OFFSET_B)),
                 ioread32((void *)((unsigned long)rab_config + offset + RAB_SLICE_ADDR_END_OFFSET_B)),
                 (unsigned long)IOREAD_L((void *)((unsigned long)rab_config + offset + RAB_SLICE_ADDR_OFFSET_OFFSET_B)),
                 flags_hw);
        }
      }
    }
  }

  // print the RAB pages and reference counter lists
  for (j = mapping_min; j < mapping_max; j++) {
    printk(KERN_INFO "PULP - RAB L1: Printing Mapping %d: \n", j);

    for (i = 0; i < RAB_L1_N_SLICES_PORT_1; i++) {
      RAB_GET_PROT(prot, l1.port_1.mappings[rab_mapping].slices[i].flags_hw);
      if (prot) {
        page_ptr_idx = l1.port_1.mappings[j].slices[i].page_ptr_idx;
        printk(KERN_INFO "Port %d, Slice %2d: page_ptrs[%2d] = %#lx, page_ptr_ref_cntrs[%2d] = %d\n", 1, i, page_ptr_idx,
               (unsigned long)l1.port_1.mappings[j].page_ptrs[page_ptr_idx], page_ptr_idx,
               l1.port_1.mappings[j].page_ptr_ref_cntrs[page_ptr_idx]);
      }
    }
  }

  return;
}
// }}}

// }}}

// Mailbox Requests {{{
/***********************************************************************************
 *
 * ███╗   ███╗██████╗  ██████╗ ██╗  ██╗    ██████╗ ███████╗ ██████╗
 * ████╗ ████║██╔══██╗██╔═══██╗╚██╗██╔╝    ██╔══██╗██╔════╝██╔═══██╗
 * ██╔████╔██║██████╔╝██║   ██║ ╚███╔╝     ██████╔╝█████╗  ██║   ██║
 * ██║╚██╔╝██║██╔══██╗██║   ██║ ██╔██╗     ██╔══██╗██╔══╝  ██║▄▄ ██║
 * ██║ ╚═╝ ██║██████╔╝╚██████╔╝██╔╝ ██╗    ██║  ██║███████╗╚██████╔╝
 * ╚═╝     ╚═╝╚═════╝  ╚═════╝ ╚═╝  ╚═╝    ╚═╝  ╚═╝╚══════╝ ╚══▀▀═╝
 *
 ***********************************************************************************/

// update {{{
void pulp_rab_update(unsigned update_req)
{
  int i, j;
  unsigned elem_mask, type;
  unsigned rab_mapping;
  unsigned stripe_idx, idx_mask, set_sel, n_slices, offset;
  RabStripeElem *elem;

  elem_mask = 0;
  RAB_UPDATE_GET_ELEM(elem_mask, update_req);
  type = 0;
  RAB_UPDATE_GET_TYPE(type, update_req);

  if (DEBUG_LEVEL_RAB_STR > 0) {
    printk(KERN_INFO "PULP - RAB: update requested, elem_mask = %#x, type = %d\n", elem_mask, type);
  }

#ifdef PROFILE_RAB_STR
  // stop the PULP timer
  iowrite32(0x1, (void *)((unsigned long)(pulp->clusters) + TIMER_STOP_OFFSET_B));

  // read the PULP timer
  n_cyc_response = ioread32((void *)((unsigned long)(pulp->clusters) + TIMER_GET_TIME_LO_OFFSET_B));
  n_cyc_tot_response += n_cyc_response;

  // reset the host clock counter
  host_reset_clock_counter();
#endif

  rab_mapping = (unsigned)pulp_rab_mapping_get_active();

  // process every data element independently
  for (i = 0; i < rab_stripe_req[rab_mapping].n_elements; i++) {
    if (!(elem_mask & (0x1 << i)))
      continue;

    elem = &rab_stripe_req[rab_mapping].elements[i];

    n_slices = elem->n_slices_per_stripe;
    stripe_idx = elem->stripe_idx;
    if (elem->type == inout) // inout -> Stripe 0, 4, 8 to Set 0, Stripe 1, 5, 9 to Set 1, etc.
      idx_mask = 0x3;
    else // in, out -> Alternate even and odd stripes to Set 0 and 1, respectively.
      idx_mask = 0x1;

    // select set of pre-allocated slices, set_offset may change on wrap around
    set_sel = (stripe_idx + elem->set_offset) & idx_mask;

    // process every slice independently
    for (j = 0; j < n_slices; j++) {
      offset =
        RAB_SLICE_BASE_OFFSET_B + RAB_SLICE_SIZE_B * (1 * RAB_L1_N_SLICES_PORT_0 + elem->slice_idxs[set_sel * n_slices + j]);

      if (DEBUG_LEVEL_RAB_STR > 3) {
        printk("stripe_idx = %d, n_slices = %d, j = %d, offset = %#x\n", stripe_idx, elem->stripes[stripe_idx].n_slices, j,
               offset);
      }

      // deactivate slice
      iowrite32(0x0, (void *)((unsigned long)(pulp->rab_config) + offset + RAB_SLICE_FLAGS_OFFSET_B));

      // set up new translations rule
      if (j < elem->stripes[stripe_idx].n_slices) {
        iowrite32(elem->stripes[stripe_idx].slice_configs[j].addr_start,
                  (void *)((unsigned long)(pulp->rab_config) + offset + RAB_SLICE_ADDR_START_OFFSET_B)); // start_addr
        iowrite32(elem->stripes[stripe_idx].slice_configs[j].addr_end,
                  (void *)((unsigned long)(pulp->rab_config) + offset + RAB_SLICE_ADDR_END_OFFSET_B)); // end_addr
        IOWRITE_L(elem->stripes[stripe_idx].slice_configs[j].addr_offset,
                  (void *)((unsigned long)(pulp->rab_config) + offset + RAB_SLICE_ADDR_OFFSET_OFFSET_B)); // offset
        iowrite32(elem->flags_hw, (void *)((unsigned long)(pulp->rab_config) + offset + RAB_SLICE_FLAGS_OFFSET_B));
#ifdef PROFILE_RAB_STR
        n_slices_updated++;
#endif
      }
    }
    // increase stripe idx counter
    elem->stripe_idx++;

    if (elem->stripe_idx == elem->n_stripes) {
      elem->stripe_idx = 0;
      if ((elem->type == inout) &&
          (elem->n_stripes & 0x3)) // inout + number of stripes not divisible by 4 -> shift set mapping
        elem->set_offset = (elem->set_offset + (elem->n_stripes & 0x3)) & 0x3;
      else if ((elem->type != inout) && (elem->n_stripes & 0x1)) // in, out + odd number of stripes -> flip set mapping
        elem->set_offset = (elem->set_offset) ? 0 : 1;

      if (DEBUG_LEVEL_RAB_STR > 0) {
        printk(KERN_INFO "PULP - RAB: elem %d stripe table wrap around.\n", i);
      }
    }
  }

  // signal ready to PULP
  iowrite32(HOST_READY | elem_mask, (void *)((unsigned long)(pulp->mbox) + MBOX_WRDATA_OFFSET_B));

#ifdef PROFILE_RAB_STR
  // read the host clock counter
  host_clk_cntr_value = host_get_clock_counter();
  n_cyc_update = host_clk_cntr_value;
  n_cyc_tot_update += n_cyc_update;

  n_updates++;

  // write the counter values to the buffers
  n_cyc_buf_response[idx_buf_response] = n_cyc_response;
  idx_buf_response++;
  n_cyc_buf_update[idx_buf_update] = n_cyc_update;
  idx_buf_update++;

  // check for buffer overflow
  if (idx_buf_response > PROFILE_RAB_N_UPDATES) {
    idx_buf_response = 0;
    printk(KERN_WARNING "PULP - RAB: n_cyc_buf_response overflow!\n");
  }
  if (idx_buf_update > PROFILE_RAB_N_UPDATES) {
    idx_buf_update = 0;
    printk(KERN_WARNING "PULP - RAB: n_cyc_buf_update overflow!\n");
  }
#endif

  if (DEBUG_LEVEL_RAB_STR > 0) {
    printk(KERN_INFO "PULP - RAB: update completed.\n");
  }

  return;
}
// }}}

// switch {{{
void pulp_rab_switch(void)
{
  int i;
  unsigned rab_mapping;

  if (DEBUG_LEVEL_RAB > 0) {
    printk(KERN_INFO "PULP - RAB: switch requested.\n");
  }

  // for debugging
  //pulp_rab_mapping_print(pulp->rab_config, 0xAAAA);

  // switch RAB mapping
  rab_mapping = (pulp_rab_mapping_get_active()) ? 0 : 1;
  pulp_rab_mapping_switch(pulp->rab_config, rab_mapping);

  // reset stripe idxs for striped mappings
  for (i = 0; i < rab_stripe_req[rab_mapping].n_elements; i++) {
    if (rab_stripe_req[rab_mapping].elements[i].type == out) // out
      rab_stripe_req[rab_mapping].elements[i].stripe_idx = 0;
    else // in, inout
      rab_stripe_req[rab_mapping].elements[i].stripe_idx = 1;
  }

  if (DEBUG_LEVEL_RAB > 0) {
    printk(KERN_INFO "PULP - RAB: switch completed.\n");
  }

  // for debugging
  //pulp_rab_mapping_print(pulp->rab_config, 0xAAAA);

  // signal ready to PULP
  iowrite32(HOST_READY, (void *)((unsigned long)(pulp->mbox) + MBOX_WRDATA_OFFSET_B));

  return;
}
// }}}

// }}}

// L2 Management {{{
/***********************************************************************************
 *
 * ██╗     ██████╗     ███╗   ███╗ ██████╗ ███╗   ███╗████████╗
 * ██║     ╚════██╗    ████╗ ████║██╔════╝ ████╗ ████║╚══██╔══╝
 * ██║      █████╔╝    ██╔████╔██║██║  ███╗██╔████╔██║   ██║
 * ██║     ██╔═══╝     ██║╚██╔╝██║██║   ██║██║╚██╔╝██║   ██║
 * ███████╗███████╗    ██║ ╚═╝ ██║╚██████╔╝██║ ╚═╝ ██║   ██║
 * ╚══════╝╚══════╝    ╚═╝     ╚═╝ ╚═════╝ ╚═╝     ╚═╝   ╚═╝
 *
 ***********************************************************************************/

// l2_init {{{
void pulp_rab_l2_init(void *rab_config)
{
  unsigned char i_port;
  for (i_port = 0; i_port < RAB_N_PORTS; ++i_port) {
    pulp_rab_l2_clear_hw(rab_config, i_port);
  }

  if (DEBUG_LEVEL_RAB > 0)
    printk(KERN_INFO "PULP - RAB L2: Initialized VRAMs to 0.\n");
}
// }}}

// l2_clear_hw {{{
void pulp_rab_l2_clear_hw(void *rab_config, unsigned char port)
{
  unsigned int i_set, i_entry, offset;
  if (RAB_L2_EN_ON_PORT[port]) {
    for (i_set = 0; i_set < RAB_L2_N_SETS; ++i_set) {
      for (i_entry = 0; i_entry < RAB_L2_N_ENTRIES_PER_SET; ++i_entry) {
        // Clear VA RAM. No need to clear PA RAM.
        offset = ((port + 1) * 0x4000) + (i_set * RAB_L2_N_ENTRIES_PER_SET * 4) + (i_entry * 4);
        iowrite32(0, (void *)((unsigned long)rab_config + offset));
        l2.set[i_set].entry[i_entry].flags = 0;
        l2.set[i_set].entry[i_entry].pfn_p = 0;
        l2.set[i_set].entry[i_entry].pfn_v = 0;
      }
      l2.set[i_set].next_entry_idx = 0;
      l2.set[i_set].is_full = 0;
    }
  }
}
// }}}

// l2_setup_entry {{{
int pulp_rab_l2_setup_entry(void *rab_config, L2Entry *tlb_entry, char port, char enable_replace)
{
  unsigned set_num, entry_num;
  unsigned data_v, data_p, off_v, off_p;

  int err = 0;
  int full = 0;

  set_num = BF_GET(tlb_entry->pfn_v, 0, 5);
  entry_num = l2.set[set_num].next_entry_idx;

  //Check if set is full
  full = pulp_rab_l2_check_availability(tlb_entry, port);
  if (full == 1 && enable_replace == 0) {
    err = 1;
    printk(KERN_WARNING "PULP - RAB L2: Port %d, Set %d: Full.\n", port, set_num);
  }
  if (full == 1 && enable_replace == 1) {
    pulp_rab_l2_invalidate_entry(rab_config, port, set_num, entry_num);
    full = 0;
  }

  if (full == 0) {
    //Set is not full. Issue a write.
    off_v = (port + 1) * 0x4000 + set_num * RAB_L2_N_ENTRIES_PER_SET * 4 + entry_num * 4;

    data_v = tlb_entry->flags;
    BF_SET(data_v, tlb_entry->pfn_v, 4, 20); // Parameterise TODO.
    iowrite32(data_v, (void *)((unsigned long)rab_config + off_v));

    off_p = (port + 1) * 0x4000 + set_num * RAB_L2_N_ENTRIES_PER_SET * 4 + entry_num * 4 +
            RAB_L2_N_ENTRIES_PER_SET * RAB_L2_N_SETS * 4; // PA RAM address
    data_p = tlb_entry->pfn_p;
    iowrite32(data_p, (void *)((unsigned long)rab_config + off_p));

    //printk("off_v = %#x, off_p = %#x \n",(unsigned)off_v, (unsigned)off_p);
    //printk("data_v = %#x, data_p = %#x \n",(unsigned)data_v, (unsigned)data_p);

    // Update kernel struct
    l2.set[set_num].entry[entry_num] = *tlb_entry;
    l2.set[set_num].next_entry_idx++;
    if (DEBUG_LEVEL_RAB > 0)
      printk(KERN_INFO "PULP - RAB L2: Port %d, Set %d, Entry %d: Setting up.\n", port, set_num, entry_num);
    if (DEBUG_LEVEL_RAB > 1) {
      printk(KERN_INFO "PULP - RAB L2: PFN_V= %#5x, PFN_P = %#5x\n", tlb_entry->pfn_v, tlb_entry->pfn_p);
    }

    if (l2.set[set_num].next_entry_idx == RAB_L2_N_ENTRIES_PER_SET) {
      l2.set[set_num].is_full = 1;
      l2.set[set_num].next_entry_idx = 0;
    }
  }

  return err;
}
// }}}

// l2_check_availability {{{
int pulp_rab_l2_check_availability(L2Entry *tlb_entry, char port)
{
  unsigned set_num;
  int full = 0;

  set_num = BF_GET(tlb_entry->pfn_v, 0, 5);

  //Check if set is full
  if (l2.set[set_num].is_full == 1) {
    full = 1;
    if (DEBUG_LEVEL_RAB > 0) {
      printk(KERN_INFO "PULP - RAB L2: Port %d, Set %d: Full.\n", port, set_num);
    }
    //return -EIO;
  }

  return full;
}
// }}}

// l2_invalidate_all_entries {{{
int pulp_rab_l2_invalidate_all_entries(void *rab_config, char port)
{
  int set_num, entry_num;

  for (set_num = 0; set_num < RAB_L2_N_SETS; set_num++) {
    for (entry_num = 0; entry_num < l2.set[set_num].next_entry_idx; entry_num++) {
      pulp_rab_l2_invalidate_entry(rab_config, port, set_num, entry_num);
    }
    l2.set[set_num].next_entry_idx = 0;
  }

  //Clear HW, even if struct has no entries.
  pulp_rab_l2_clear_hw(rab_config, port);

  return 0;
}
// }}}

// l2_invalidate_entry {{{
int pulp_rab_l2_invalidate_entry(void *rab_config, char port, int set_num, int entry_num)
{
  unsigned data;
  struct page *page_old;

  if (DEBUG_LEVEL_RAB > 1) {
    printk(KERN_INFO "PULP - RAB L2: Port %d, Set %d, Entry %d: Freeing.\n", port, set_num, entry_num);
  }
  data = l2.set[set_num].entry[entry_num].flags;
  data = data >> 1;
  data = data << 1; // LSB is now zero.
  l2.set[set_num].entry[entry_num].flags = data; // Update kernel struct
  BF_SET(data, l2.set[set_num].entry[entry_num].pfn_v, 4, 20); // Parameterise TODO.
  iowrite32(data, (void *)((unsigned long)rab_config + ((port + 1) * 0x4000) + (set_num * RAB_L2_N_ENTRIES_PER_SET * 4) +
                           (entry_num * 4)));

  // unlock pages and invalidate cache.
  page_old = l2.set[set_num].entry[entry_num].page_ptr;

  if (page_old) {
    // cache invalidation (in case of prefetching/speculation...)
    if (!(data & 0x8))
      pulp_mem_cache_inv(page_old, 0, PAGE_SIZE);

    // unpin user-space memory
    if (!PageReserved(page_old))
      SetPageDirty(page_old);
    put_page(page_old);

    // reset page_ptr
    l2.set[set_num].entry[entry_num].page_ptr = NULL;
  }

  return 0;
}
// }}}

// l2_print_all_entries {{{
int pulp_rab_l2_print_all_entries(char port)
{
  int set_num, entry_num;
  printk(KERN_INFO "PULP - RAB L2: Printing config of Port %d\n", port);
  for (set_num = 0; set_num < RAB_L2_N_SETS; set_num++) {
    for (entry_num = 0; entry_num < l2.set[set_num].next_entry_idx; entry_num++) {
      printk(KERN_INFO "Set %d, Entry %d: PFN_V = %#x, PFN_P = %#x, Flags = %#x\n", set_num, entry_num,
             l2.set[set_num].entry[entry_num].pfn_v, l2.set[set_num].entry[entry_num].pfn_p,
             l2.set[set_num].entry[entry_num].flags);
    }
  }
  return 0;
}
// }}}

// l2_print_valid_entries {{{
int pulp_rab_l2_print_valid_entries(char port)
{
  int set_num, entry_num;
  printk(KERN_INFO "PULP - RAB L2: Printing valid entries of Port %d\n", port);
  for (set_num = 0; set_num < RAB_L2_N_SETS; set_num++) {
    for (entry_num = 0; entry_num < l2.set[set_num].next_entry_idx; entry_num++) {
      if (l2.set[set_num].entry[entry_num].flags & 0x1) {
        printk(KERN_INFO "Set %d, Entry %d: PFN_V = %#x, PFN_P = %#x, Flags = %#x\n", set_num, entry_num,
               l2.set[set_num].entry[entry_num].pfn_v, l2.set[set_num].entry[entry_num].pfn_p,
               l2.set[set_num].entry[entry_num].flags);
      }
    }
  }
  return 0;
}
// }}}

//////// Other functions
// pulp_rab_l2_replace_entry()
// pulp_rab_l2_find_entry_to_replace()

// The user will give preference as L1 or L2. Default option is L1 . try to group all nearby L1 together and call ioctl, same as before.
// If all slices are used up, give back error for now. Later, we will make them fill L2 in case L1 is full.
// group all L2 together and call ioctl. There should be only one ioctl for all of L2.
// Further enhancement would be to use some algorithm to dynamically assign the mapping to L1 or L2 based on region size and frequency of occurance.

// }}}

// IOCTL Requests {{{
/***********************************************************************************
 *
 * ██╗ ██████╗  ██████╗████████╗██╗         ██████╗ ███████╗ ██████╗
 * ██║██╔═══██╗██╔════╝╚══██╔══╝██║         ██╔══██╗██╔════╝██╔═══██╗
 * ██║██║   ██║██║        ██║   ██║         ██████╔╝█████╗  ██║   ██║
 * ██║██║   ██║██║        ██║   ██║         ██╔══██╗██╔══╝  ██║▄▄ ██║
 * ██║╚██████╔╝╚██████╗   ██║   ███████╗    ██║  ██║███████╗╚██████╔╝
 * ╚═╝ ╚═════╝  ╚═════╝   ╚═╝   ╚══════╝    ╚═╝  ╚═╝╚══════╝ ╚══▀▀═╝
 *
 ***********************************************************************************/

// req {{{
long pulp_rab_req(void *rab_config, RabSliceReq *rab_slice_req)
{
  int err = 0, i, j;
  long retval = 0;
  unsigned size_b;

  // what get_user_pages needs
  struct page **pages;
  unsigned len;

  // what mem_map_sg needs needs
  unsigned *addr_start_vec;
  unsigned *addr_end_vec;
  unsigned long *addr_offset_vec;
  unsigned *page_idxs_start;
  unsigned *page_idxs_end;
  unsigned n_segments;

  // needed for cache flushing
  unsigned offset_start, offset_end;

  // needed for L2 TLB
  unsigned char rab_lvl;
  unsigned char rab_use_l1;
  unsigned *pfn_v_vec;
  unsigned *pfn_p_vec;
  L2Entry l2_entry_request;
  L2Entry *l2_entry = &l2_entry_request;
  unsigned n_free_slices;

  n_segments = 1;
  rab_lvl = rab_slice_req->rab_lvl;
  size_b = rab_slice_req->addr_end - rab_slice_req->addr_start;

  if (DEBUG_LEVEL_RAB > 1) {
    printk(KERN_INFO "PULP: New RAB request:\n");
    printk(KERN_INFO "PULP: addr_start = %#x.\n", rab_slice_req->addr_start);
    printk(KERN_INFO "PULP: addr_end   = %#x.\n", rab_slice_req->addr_end);
    printk(KERN_INFO "PULP: flags_hw   = %#x.\n", rab_slice_req->flags_hw);
    printk(KERN_INFO "PULP: rab_port   = %d.\n", rab_slice_req->rab_port);
    printk(KERN_INFO "PULP: rab_lvl    = %d.\n", rab_lvl);
    printk(KERN_INFO "PULP: date_exp   = %d.\n", rab_slice_req->date_exp);
    printk(KERN_INFO "PULP: date_cur   = %d.\n", rab_slice_req->date_cur);
  }

  // check type of remapping
  if ((rab_slice_req->rab_port == 0) || (rab_slice_req->addr_start == L3_MEM_BASE_ADDR))
    BIT_SET(rab_slice_req->flags_drv, RAB_FLAGS_DRV_CONST | RAB_FLAGS_DRV_EVERY);
  else // for now, set up every request on every mapping
    BIT_SET(rab_slice_req->flags_drv, RAB_FLAGS_DRV_EVERY);

  rab_use_l1 = 0;
  if (BIT_GET(rab_slice_req->flags_drv, RAB_FLAGS_DRV_CONST)) { // constant remapping
    switch (rab_slice_req->addr_start) {
    case MBOX_H_BASE_ADDR:
      rab_slice_req->addr_offset = MBOX_BASE_ADDR + MBOX_SIZE_B; // Interface 1
      break;

    case L2_MEM_H_BASE_ADDR:
      rab_slice_req->addr_offset = L2_MEM_BASE_ADDR;
      break;

    case PULP_H_BASE_ADDR:
      rab_slice_req->addr_offset = PULP_BASE_ADDR;
      break;

    case L3_MEM_BASE_ADDR: // - port 1
      rab_slice_req->addr_offset = L3_MEM_H_BASE_ADDR;
      break;

      // also route accesses to the contiguous L3 through the coherent port
      //BIT_SET(rab_slice_req->flags_hw, RAB_FLAGS_HW_CC);

    default:
      break;
    }

    len = 1;
    rab_use_l1 = 1;
  } else { // address translation required
    // number of pages
    len = pulp_mem_get_num_pages(rab_slice_req->addr_start, size_b);

    // get and lock user-space pages
    err =
      pulp_mem_get_user_pages(&pages, rab_slice_req->addr_start, len, BIT_GET(rab_slice_req->flags_hw, RAB_FLAGS_HW_WRITE));
    if (err) {
      printk(KERN_WARNING "PULP - RAB: Locking of user-space pages failed.\n");
      return (long)err;
    }

    // where to place the mapping ?
    if (rab_lvl == 0) {
      // Check the number of segments and the number of available slices.
      n_segments = pulp_mem_check_num_sg(&pages, len);
      n_free_slices = pulp_rab_num_free_slices(rab_slice_req);
      if (n_free_slices < n_segments)
        rab_use_l1 = 0; // use L2 if number of free slices in L1 is not sufficient.
      else
        rab_use_l1 = 1;
    } else {
      rab_use_l1 = rab_lvl % 2;
    }
  }

  if (rab_use_l1 == 1) { // use L1 TLB

    if (!BIT_GET(rab_slice_req->flags_drv, RAB_FLAGS_DRV_CONST)) { // not constant remapping
      // virtual to physcial address translation + segmentation
      n_segments = pulp_mem_map_sg(&addr_start_vec, &addr_end_vec, &addr_offset_vec, &page_idxs_start, &page_idxs_end,
                                   &pages, len, rab_slice_req->addr_start, rab_slice_req->addr_end);
      if (n_segments < 1) {
        printk(KERN_WARNING "PULP - RAB: Virtual to physical address translation failed.\n");
        return (long)n_segments;
      }
    }

    /*
     *  setup the slices
     */
    // to do: protect with semaphore!?
    for (i = 0; i < n_segments; i++) {
      if (!BIT_GET(rab_slice_req->flags_drv, RAB_FLAGS_DRV_CONST)) {
        rab_slice_req->addr_start = addr_start_vec[i];
        rab_slice_req->addr_end = addr_end_vec[i];
        rab_slice_req->addr_offset = addr_offset_vec[i];
        rab_slice_req->page_idx_start = page_idxs_start[i];
        rab_slice_req->page_idx_end = page_idxs_end[i];
      }

      // some requests need to be set up for every mapping
      for (j = 0; j < RAB_L1_N_MAPPINGS_PORT_1; j++) {
        if ((rab_slice_req->rab_port == 1) && BIT_GET(rab_slice_req->flags_drv, RAB_FLAGS_DRV_EVERY))
          rab_slice_req->rab_mapping = j;

        if (rab_slice_req->rab_mapping == j) {
          //  check for free field in page_ptrs list
          if (!i && (rab_slice_req->rab_port == 1)) {
            err = pulp_rab_page_ptrs_get_field(rab_slice_req);
            if (err) {
              return (long)err;
            }
          }

          // get a free slice
          err = pulp_rab_slice_get(rab_slice_req);
          if (err) {
            return (long)err;
          }

          // free memory of slices to be re-configured
          pulp_rab_slice_free(rab_config, rab_slice_req);

          // setup slice
          err = pulp_rab_slice_setup(rab_config, rab_slice_req, pages);
          if (err) {
            return (long)err;
          }
        }
      }

      // flush caches
      if (!BIT_GET(rab_slice_req->flags_drv, RAB_FLAGS_DRV_CONST) && !BIT_GET(rab_slice_req->flags_hw, RAB_FLAGS_HW_CC)) {
        for (j = page_idxs_start[i]; j < (page_idxs_end[i] + 1); j++) {
          // flush the whole page?
          if (!i)
            offset_start = BF_GET(addr_start_vec[i], 0, PAGE_SHIFT);
          else
            offset_start = 0;

          if (i == (n_segments - 1))
            offset_end = BF_GET(addr_end_vec[i], 0, PAGE_SHIFT);
          else
            offset_end = PAGE_SIZE;

          pulp_mem_cache_flush(pages[j], offset_start, offset_end);
        }
      }
    } // for n_segments
  } else { // use L2 TLB
    // virtual to physical page frame number translation for each page
    err = pulp_mem_l2_get_entries(&pfn_v_vec, &pfn_p_vec, &pages, len, rab_slice_req->addr_start);
    l2_entry->flags = rab_slice_req->flags_hw;

    for (i = 0; i < len; i++) {
      l2_entry->pfn_v = pfn_v_vec[i];
      l2_entry->pfn_p = pfn_p_vec[i];
      if (pages)
        l2_entry->page_ptr = pages[i];
      else
        l2_entry->page_ptr = 0;

      // setup entry
      err = pulp_rab_l2_setup_entry(rab_config, l2_entry, rab_slice_req->rab_port, 0);
      if (err) {
        return (long)err;
      }

      // flush caches
      if (!BIT_GET(rab_slice_req->flags_drv, RAB_FLAGS_DRV_CONST) && !BIT_GET(rab_slice_req->flags_hw, RAB_FLAGS_HW_CC)) {
        // flush the whole page?
        pulp_mem_cache_flush(pages[i], 0, PAGE_SIZE);
      }
    } // for (i=0; i<len; i++) {

    if (!BIT_GET(rab_slice_req->flags_drv, RAB_FLAGS_DRV_CONST)) {
      kfree(pages); // No need of pages since we have the individual page ptr for L2 entry in page_ptr.
    }
  }

  // kfree
  if (!BIT_GET(rab_slice_req->flags_drv, RAB_FLAGS_DRV_CONST) && rab_use_l1) {
    kfree(addr_start_vec);
    kfree(addr_end_vec);
    kfree(addr_offset_vec);
    kfree(page_idxs_start);
    kfree(page_idxs_end);
  }
  if (rab_use_l1 == 0) {
    kfree(pfn_v_vec);
    kfree(pfn_p_vec);
  }

  return retval;
}
// }}}

// req_striped {{{
long pulp_rab_req_striped(void *rab_config, unsigned long arg)
{
  int err = 0, i, j, k;
  long retval = 0;

  // to read from user space
  unsigned long n_bytes_read, n_bytes_left;
  unsigned byte;

  // what we get from user space
  unsigned size_b;

  // what get_user_pages needs
  struct page **pages;
  unsigned len;

  // what mem_map_sg needs needs
  unsigned *addr_start_vec;
  unsigned *addr_end_vec;
  unsigned long *addr_offset_vec;
  unsigned *page_idxs_start;
  unsigned *page_idxs_end;
  unsigned n_segments;

  // needed for cache flushing
  unsigned offset_start, offset_end;

  // needed for RAB management
  RabSliceReq rab_slice_request;
  RabSliceReq *rab_slice_req = &rab_slice_request;
  unsigned n_slices;

  // needed for RAB striping
  RabStripeReqUser rab_stripe_req_user;
  RabStripeElemUser *rab_stripe_elem_user;
  RabStripeElem *rab_stripe_elem;
  unsigned *stripe_addr_start;
  unsigned *stripe_addr_end;
  unsigned addr_start;
  unsigned addr_end;
  unsigned long addr_offset;
  unsigned seg_idx_start;
  unsigned seg_idx_end;

#ifdef PROFILE_RAB_STR
  // reset the host clock counter
  host_reset_clock_counter();
#endif

  if (DEBUG_LEVEL_RAB > 1) {
    printk(KERN_INFO "PULP - RAB: New striped RAB request.\n");
  }

  /*
   * get:
   * - ID, number of elements to stripe
   * - user-space address of array holding the RabStripeElemUser structs (1 struct per element)
   */
  // get transfer data from user space - arg already checked above
  byte = 0;
  n_bytes_left = sizeof(RabStripeReqUser);
  n_bytes_read = n_bytes_left;
  while (n_bytes_read > 0) {
    n_bytes_left =
      __copy_from_user((void *)((char *)(&rab_stripe_req_user) + byte), (void __user *)((char *)arg + byte), n_bytes_read);
    byte += (n_bytes_read - n_bytes_left);
    n_bytes_read = n_bytes_left;
  }
  if (DEBUG_LEVEL_RAB_STR > 1) {
    printk(KERN_INFO "PULP - RAB: id = %d, n_elements = %d\n", rab_stripe_req_user.id, rab_stripe_req_user.n_elements);
  }
  if (DEBUG_LEVEL_RAB_STR > 2) {
    printk(KERN_INFO "PULP - RAB: rab_stripe_elem_user_addr = %lx\n", rab_stripe_req_user.rab_stripe_elem_user_addr);
  }

  // allocate memory to hold the array of RabStripeElemUser structs (1 struct per element)
  rab_stripe_elem_user =
    (RabStripeElemUser *)kmalloc((size_t)(rab_stripe_req_user.n_elements * sizeof(RabStripeElemUser)), GFP_KERNEL);
  if (rab_stripe_elem_user == NULL) {
    printk(KERN_WARNING "PULP - RAB: Memory allocation failed.\n");
    return -ENOMEM;
  }

  /*
   * get:
   * - array of RabStripeElemUser structs
   */
  // get data from user space
  byte = 0;
  n_bytes_left = rab_stripe_req_user.n_elements * sizeof(RabStripeElemUser);
  n_bytes_read = n_bytes_left;
  while (n_bytes_read > 0) {
    n_bytes_left = copy_from_user((void *)((char *)rab_stripe_elem_user + byte),
                                  (void __user *)((unsigned long)rab_stripe_req_user.rab_stripe_elem_user_addr + byte),
                                  n_bytes_read);
    byte += (n_bytes_read - n_bytes_left);
    n_bytes_read = n_bytes_left;
  }

  // allocate memory to hold the array of RabStripeElem structs (1 struct per element)
  rab_stripe_elem = (RabStripeElem *)kmalloc((size_t)(rab_stripe_req_user.n_elements * sizeof(RabStripeElem)), GFP_KERNEL);
  if (rab_stripe_elem == NULL) {
    printk(KERN_WARNING "PULP - RAB: Memory allocation failed.\n");
    return -ENOMEM;
  }

  // process every data element independently
  for (i = 0; i < rab_stripe_req_user.n_elements; i++) {
    /*
     * preparations
     */
    // compute the maximum number of required slices (per stripe)
    n_slices = rab_stripe_elem_user[i].max_stripe_size_b / PAGE_SIZE;
    if (n_slices * PAGE_SIZE < rab_stripe_elem_user[i].max_stripe_size_b)
      n_slices++; // remainder
    n_slices++; // non-aligned

    if (DEBUG_LEVEL_RAB_STR > 1) {
      printk(KERN_INFO "PULP - RAB: Element %d, n_slices = %d\n", i, n_slices);
    }

    // fill RabStripeElem struct for further use
    rab_stripe_elem[i].id = rab_stripe_elem_user[i].id;
    rab_stripe_elem[i].type = rab_stripe_elem_user[i].type;
    rab_stripe_elem[i].n_slices_per_stripe = n_slices;
    rab_stripe_elem[i].set_offset = 0;
    rab_stripe_elem[i].n_stripes = rab_stripe_elem_user[i].n_stripes;
    rab_stripe_elem[i].flags_hw = rab_stripe_elem_user[i].flags | 0x2; // write only does not work in the hardware!

    // compute the actual number of required slices
    if (rab_stripe_elem[i].type == inout)
      rab_stripe_elem[i].n_slices = 4 * n_slices; // double buffering: *2 + inout: *2
    else
      rab_stripe_elem[i].n_slices = 2 * n_slices; // double buffering: *2

    // set stripe_idx = stripe to configure at first update request
    if (rab_stripe_elem[i].type == out)
      rab_stripe_elem[i].stripe_idx = 1; //0;
    else
      rab_stripe_elem[i].stripe_idx = 1;

    // allocate memory to hold array of slice idxs - slices will be requested later
    rab_stripe_elem[i].slice_idxs =
      (unsigned *)kmalloc((size_t)(rab_stripe_elem[i].n_slices * sizeof(unsigned)), GFP_KERNEL);
    if (rab_stripe_elem[i].slice_idxs == NULL) {
      printk(KERN_WARNING "PULP - RAB: Memory allocation failed.\n");
      return -ENOMEM;
    }

    /*
     * get actual striping data from user space:
     * - array of stripe start/end addresses (2 32b user-space addr per stripe)
     */
    // allocate memory to hold addr_start and addr_end array
    stripe_addr_start = (unsigned *)kmalloc((size_t)(rab_stripe_elem[i].n_stripes * sizeof(unsigned)), GFP_KERNEL);
    if (stripe_addr_start == NULL) {
      printk(KERN_WARNING "PULP - RAB: Memory allocation failed.\n");
      return -ENOMEM;
    }
    stripe_addr_end = (unsigned *)kmalloc((size_t)(rab_stripe_elem[i].n_stripes * sizeof(unsigned)), GFP_KERNEL);
    if (stripe_addr_end == NULL) {
      printk(KERN_WARNING "PULP - RAB: Memory allocation failed.\n");
      return -ENOMEM;
    }

    // get data from user space
    byte = 0;
    n_bytes_left = rab_stripe_elem_user[i].n_stripes * sizeof(unsigned);
    n_bytes_read = n_bytes_left;
    while (n_bytes_read > 0) {
      n_bytes_left = copy_from_user((void *)((char *)stripe_addr_start + byte),
                                    (void __user *)((unsigned long)rab_stripe_elem_user[i].stripe_addr_start + byte),
                                    n_bytes_read);
      byte += (n_bytes_read - n_bytes_left);
      n_bytes_read = n_bytes_left;
    }

    byte = 0;
    n_bytes_left = rab_stripe_elem_user[i].n_stripes * sizeof(unsigned);
    n_bytes_read = n_bytes_left;
    while (n_bytes_read > 0) {
      n_bytes_left = copy_from_user((void *)((char *)stripe_addr_end + byte),
                                    (void __user *)((unsigned long)rab_stripe_elem_user[i].stripe_addr_end + byte),
                                    n_bytes_read);
      byte += (n_bytes_read - n_bytes_left);
      n_bytes_read = n_bytes_left;
    }

    addr_start = stripe_addr_start[0];
    addr_end = stripe_addr_end[rab_stripe_elem[i].n_stripes - 1];
    size_b = addr_end - addr_start;

    if (DEBUG_LEVEL_RAB_STR > 2) {
      printk(KERN_INFO "PULP - RAB: addr_start = %#x \n", addr_start);
      printk(KERN_INFO "PULP - RAB: addr_end   = %#x \n", addr_end);
      printk(KERN_INFO "PULP - RAB: size_b     = %#x \n", size_b);
    }

    /*
     * get user-space pages ready
     */
    // number of pages
    len = pulp_mem_get_num_pages(addr_start, size_b);

#ifdef PROFILE_RAB_STR
    n_pages_setup += len;
#endif

#ifdef PROFILE_RAB_STR
    // read the host clock counter
    host_clk_cntr_value = host_get_clock_counter();
#endif

    // get and lock user-space pages
    err = pulp_mem_get_user_pages(&pages, addr_start, len, BIT_GET(rab_stripe_elem[i].flags_hw, RAB_FLAGS_HW_WRITE));
    if (err) {
      printk(KERN_WARNING "PULP: Locking of user-space pages failed.\n");
      return err;
    }

#ifdef PROFILE_RAB_STR
    host_clk_cntr_value_start = host_clk_cntr_value;

    // read the host clock counter
    host_clk_cntr_value = host_get_clock_counter();
    n_cyc_get_user_pages = host_clk_cntr_value - host_clk_cntr_value_start;
    n_cyc_tot_get_user_pages += n_cyc_get_user_pages;
#endif

    // virtual to physcial address translation + segmentation
    n_segments = pulp_mem_map_sg(&addr_start_vec, &addr_end_vec, &addr_offset_vec, &page_idxs_start, &page_idxs_end, &pages,
                                 len, addr_start, addr_end);
    if (n_segments < 1) {
      printk(KERN_WARNING "PULP - RAB: Virtual to physical address translation failed.\n");
      return n_segments;
    }

#ifdef PROFILE_RAB_STR
    host_clk_cntr_value_start = host_clk_cntr_value;

    // read the host clock counter
    host_clk_cntr_value = host_get_clock_counter();
    n_cyc_map_sg = host_clk_cntr_value - host_clk_cntr_value_start;
    n_cyc_tot_map_sg += n_cyc_map_sg;
#endif

    if (!BIT_GET(rab_stripe_elem[i].flags_hw, RAB_FLAGS_HW_CC)) {
      // flush caches for all segments
      for (j = 0; j < n_segments; j++) {
        for (k = page_idxs_start[j]; k < (page_idxs_end[j] + 1); k++) {
          // flush the whole page?
          if (!j)
            offset_start = BF_GET(addr_start_vec[j], 0, PAGE_SHIFT);
          else
            offset_start = 0;

          if (j == (n_segments - 1))
            offset_end = BF_GET(addr_end_vec[j], 0, PAGE_SHIFT);
          else
            offset_end = PAGE_SIZE;

          pulp_mem_cache_flush(pages[k], offset_start, offset_end);
        }
      }
    }

#ifdef PROFILE_RAB_STR
    host_clk_cntr_value_start = host_clk_cntr_value;

    // read the host clock counter
    host_clk_cntr_value = host_get_clock_counter();
    n_cyc_cache_flush = host_clk_cntr_value - host_clk_cntr_value_start;
    n_cyc_tot_cache_flush += n_cyc_cache_flush;
#endif

    /*
     * generate the striping table
     */
    // allocate memory to hold array of RabStripe structs
    rab_stripe_elem[i].stripes = (RabStripe *)kmalloc((size_t)rab_stripe_elem[i].n_stripes * sizeof(RabStripe), GFP_KERNEL);
    if (rab_stripe_elem[i].stripes == NULL) {
      printk(KERN_WARNING "PULP - MEM: Memory allocation failed.\n");
      return -ENOMEM;
    }

    seg_idx_start = 0;
    seg_idx_end = 0;

    // loop over stripes
    for (j = 0; j < rab_stripe_elem[i].n_stripes; j++) {
      // determine the segment indices
      while (((seg_idx_start + 1) < n_segments) && (stripe_addr_start[j] >= addr_start_vec[seg_idx_start + 1])) {
        seg_idx_start++;
      }
      while ((seg_idx_end < n_segments) && (stripe_addr_end[j] > addr_end_vec[seg_idx_end])) {
        seg_idx_end++;
      }

      if (DEBUG_LEVEL_RAB_STR > 3) {
        printk(KERN_INFO "PULP - RAB: Stripe %d: seg_idx_start = %d, seg_idx_end = %d \n", j, seg_idx_start, seg_idx_end);
      }

      n_slices = seg_idx_end - seg_idx_start + 1; // number of required slices
      rab_stripe_elem[i].stripes[j].n_slices = n_slices;
      if (n_slices > (rab_stripe_elem[i].n_slices_per_stripe)) {
        printk(KERN_WARNING "PULP - RAB: Stripe %d of Element %d touches too many memory segments.\n", j, i);
        //printk(KERN_INFO "%d slices reserved, %d segments\n",elem_cur->n_slices_per_stripe, n_segments);
        //printk(KERN_INFO "start segment = %d, end segment = %d\n",seg_idx_start,seg_idx_end);
      }

      // allocate memory to hold array of RabStripeSlice structs
      rab_stripe_elem[i].stripes[j].slice_configs =
        (RabStripeSlice *)kmalloc((size_t)n_slices * sizeof(RabStripeSlice), GFP_KERNEL);
      if (rab_stripe_elem[i].stripes[j].slice_configs == NULL) {
        printk(KERN_WARNING "PULP - MEM: Memory allocation failed.\n");
        return -ENOMEM;
      }

      // extract the addr of segments, loop over slices
      for (k = 0; k < n_slices; k++) {
        // virtual start + physical addr
        if (k == 0) {
          addr_start = stripe_addr_start[j];
          addr_offset = addr_offset_vec[seg_idx_start];
          // inter-page offset: for multi-page segments
          addr_offset += (unsigned long)((BF_GET(addr_start, PAGE_SHIFT, 32 - PAGE_SHIFT) << PAGE_SHIFT) -
                                         (BF_GET(addr_start_vec[seg_idx_start], PAGE_SHIFT, 32 - PAGE_SHIFT) << PAGE_SHIFT));
          // intra-page offset: no additional offset for first slice of first stripe
          if (j != 0)
            addr_offset += (unsigned long)(stripe_addr_start[j] & BIT_MASK_GEN(PAGE_SHIFT));
        } else { // ( k < n_slices )
          addr_start = addr_start_vec[seg_idx_start + k];
          addr_offset = addr_offset_vec[seg_idx_start + k];
        }
        // virtual end addr
        if (k < (n_slices - 1)) // end addr defined by segment end
          addr_end = addr_end_vec[seg_idx_start + k];
        else // last slice, end at stripe end
          addr_end = stripe_addr_end[j];

        // write data to table
        rab_stripe_elem[i].stripes[j].slice_configs[k].addr_start = addr_start;
        rab_stripe_elem[i].stripes[j].slice_configs[k].addr_end = addr_end;
        rab_stripe_elem[i].stripes[j].slice_configs[k].addr_offset = addr_offset;
      }
    }

    if (DEBUG_LEVEL_RAB_STR > 3) {
      for (j = 0; j < rab_stripe_elem[i].n_stripes; j++) {
        printk(KERN_INFO "PULP - RAB: Stripe %d:\n", j);
        for (k = 0; k < rab_stripe_elem[i].stripes[j].n_slices; k++) {
          printk(KERN_INFO "addr_start [%d] %#x\n", k, rab_stripe_elem[i].stripes[j].slice_configs[k].addr_start);
          printk(KERN_INFO "addr_end   [%d] %#x\n", k, rab_stripe_elem[i].stripes[j].slice_configs[k].addr_end);
          printk(KERN_INFO "addr_offset[%d] %#lx\n", k, rab_stripe_elem[i].stripes[j].slice_configs[k].addr_offset);
        }
        printk(KERN_INFO "\n");
      }
    }

    /*
     *  request the slices
     */
    rab_slice_req->rab_port = 1;
    rab_slice_req->rab_mapping = rab_stripe_req_user.id % RAB_L1_N_MAPPINGS_PORT_1;
    rab_slice_req->flags_hw = rab_stripe_elem[i].flags_hw;

    // do not overwrite any remappings, the remappings will be freed manually
    rab_slice_req->date_cur = 0x1;
    rab_slice_req->date_exp = RAB_MAX_DATE; // also avoid check in pulp_rab_slice_setup

    // assign all pages to all slices
    rab_slice_req->page_idx_start = page_idxs_start[0];
    rab_slice_req->page_idx_end = page_idxs_end[n_segments - 1];

    //  check for free field in page_ptrs list
    err = pulp_rab_page_ptrs_get_field(rab_slice_req);
    if (err) {
      return err;
    }
    rab_stripe_elem[i].page_ptr_idx = rab_slice_req->page_ptr_idx;

    for (j = 0; j < rab_stripe_elem[i].n_slices; j++) {
      // set up only the used slices of the first stripe, the others need just to be requested
      if (j > (rab_stripe_elem[i].stripes[0].n_slices - 1)) {
        rab_slice_req->addr_start = 0;
        rab_slice_req->addr_end = 0;
        rab_slice_req->addr_offset = 0;
        rab_slice_req->flags_hw = rab_stripe_elem[i].flags_hw;
        BIT_CLEAR(rab_slice_req->flags_hw, RAB_FLAGS_HW_EN); // do not yet enable
      } else {
        rab_slice_req->addr_start = rab_stripe_elem[i].stripes[0].slice_configs[j].addr_start;
        rab_slice_req->addr_end = rab_stripe_elem[i].stripes[0].slice_configs[j].addr_end;
        rab_slice_req->addr_offset = rab_stripe_elem[i].stripes[0].slice_configs[j].addr_offset;
        rab_slice_req->flags_hw = rab_stripe_elem[i].flags_hw;
      }
      // force check in pulp_rab_slice_setup
      rab_slice_req->flags_drv = 0;
      if (j > 0)
        BIT_SET(rab_slice_req->flags_drv, RAB_FLAGS_DRV_STRIPED); // striped mode, not constant

      // get a free slice
      err = pulp_rab_slice_get(rab_slice_req);
      if (err) {
        return err;
      }
      rab_stripe_elem[i].slice_idxs[j] = rab_slice_req->rab_slice;

      // free memory of slices to be re-configured
      pulp_rab_slice_free(rab_config, rab_slice_req);

      // set up slice
      err = pulp_rab_slice_setup(rab_config, rab_slice_req, pages);
      if (err) {
        return err;
      }
    }

    if (DEBUG_LEVEL_RAB > 2) {
      printk(KERN_INFO "PULP - RAB: Element %d: \n", i);
      printk(KERN_INFO "PULP - RAB: Striped slices: \n");
      for (j = 0; j < rab_stripe_elem[i].n_slices; j++) {
        printk(KERN_INFO "%d, ", rab_stripe_elem[i].slice_idxs[j]);
      }
      printk(KERN_INFO "\n");
    }

    // free memory
    kfree(stripe_addr_start);
    kfree(stripe_addr_end);

    // free memory - allocated inside pulp_mem_map_sg()
    kfree(addr_start_vec);
    kfree(addr_end_vec);
    kfree(addr_offset_vec);
    kfree(page_idxs_start);
    kfree(page_idxs_end);
  } // for n_elements

  // fill RabStripeReq struct for further use
  rab_stripe_req[rab_slice_req->rab_mapping].id = rab_stripe_req_user.id;
  rab_stripe_req[rab_slice_req->rab_mapping].n_elements = rab_stripe_req_user.n_elements;
  rab_stripe_req[rab_slice_req->rab_mapping].elements = &rab_stripe_elem[0];

  // free memory
  kfree(rab_stripe_elem_user);

#ifdef PROFILE_RAB_STR
  // read the host clock counter
  host_clk_cntr_value = host_get_clock_counter();
  n_cyc_setup = host_clk_cntr_value;
  n_cyc_tot_setup += n_cyc_setup;

  // write the counter values to the buffers
  n_cyc_buf_setup[idx_buf_setup] = n_cyc_setup;
  idx_buf_setup++;
  n_cyc_buf_cache_flush[idx_buf_cache_flush] = n_cyc_cache_flush;
  idx_buf_cache_flush++;
  n_cyc_buf_get_user_pages[idx_buf_get_user_pages] = n_cyc_get_user_pages;
  idx_buf_get_user_pages++;
  n_cyc_buf_map_sg[idx_buf_map_sg] = n_cyc_map_sg;
  idx_buf_map_sg++;

  // check for buffer overflow
  if (idx_buf_setup > PROFILE_RAB_N_REQUESTS) {
    idx_buf_setup = 0;
    printk(KERN_WARNING "PULP - RAB: n_cyc_buf_setup overflow!\n");
  }
  if (idx_buf_cache_flush > PROFILE_RAB_N_ELEMENTS) {
    idx_buf_cache_flush = 0;
    printk(KERN_WARNING "PULP - RAB: n_cyc_buf_cache_flush overflow!\n");
  }
  if (idx_buf_get_user_pages > PROFILE_RAB_N_ELEMENTS) {
    idx_buf_get_user_pages = 0;
    printk(KERN_WARNING "PULP - RAB: n_cyc_buf_get_user_pages overflow!\n");
  }
  if (idx_buf_map_sg > PROFILE_RAB_N_ELEMENTS) {
    idx_buf_map_sg = 0;
    printk(KERN_WARNING "PULP - RAB: n_cyc_buf_map_sg overflow!\n");
  }
#endif

  return retval;
}
// }}}

// free {{{
/***********************************************************************************
 *
 * ██╗ ██████╗  ██████╗████████╗██╗         ███████╗██████╗ ███████╗███████╗
 * ██║██╔═══██╗██╔════╝╚══██╔══╝██║         ██╔════╝██╔══██╗██╔════╝██╔════╝
 * ██║██║   ██║██║        ██║   ██║         █████╗  ██████╔╝█████╗  █████╗
 * ██║██║   ██║██║        ██║   ██║         ██╔══╝  ██╔══██╗██╔══╝  ██╔══╝
 * ██║╚██████╔╝╚██████╗   ██║   ███████╗    ██║     ██║  ██║███████╗███████╗
 * ╚═╝ ╚═════╝  ╚═════╝   ╚═╝   ╚══════╝    ╚═╝     ╚═╝  ╚═╝╚══════╝╚══════╝
 *
 ***********************************************************************************/

void pulp_rab_free(void *rab_config, unsigned date, bool fixed)
{
  int i, j, k;

  // needed for RAB management
  RabSliceReq rab_slice_request;
  RabSliceReq *rab_slice_req = &rab_slice_request;
  unsigned n_slices;
  unsigned n_mappings;

  // get current date
  rab_slice_req->date_cur = date;
  rab_slice_req->flags_drv = 0;

  // check every slice on every port for every mapping
  for (i = 0; i < RAB_N_PORTS; i++) {
    rab_slice_req->rab_port = i;

    if (i == 0) {
      n_mappings = 1;
      n_slices = RAB_L1_N_SLICES_PORT_0;
    } else { // Port 1
      n_mappings = RAB_L1_N_MAPPINGS_PORT_1;
      n_slices = RAB_L1_N_SLICES_PORT_1;
    }

    for (j = 0; j < n_mappings; j++) {
      rab_slice_req->rab_mapping = j;
      for (k = 0; k < n_slices; k++) {
        rab_slice_req->rab_slice = k;

        if (rab_slice_req->rab_port == 1) {
          rab_slice_req->flags_drv = l1.port_1.mappings[j].slices[k].flags_drv;
          if (BIT_GET(rab_slice_req->flags_drv, RAB_FLAGS_DRV_EVERY) && (j == n_mappings - 1))
            BIT_CLEAR(rab_slice_req->flags_drv,
                      RAB_FLAGS_DRV_EVERY); // unlock and release pages when freeing the last mapping
        } else
          BIT_SET(rab_slice_req->flags_drv, RAB_FLAGS_DRV_CONST); // Port 0 can only hold constant mappings

        if (fixed) {
          BIT_SET(rab_slice_req->flags_drv, RAB_FLAGS_DRV_FIXED);
        } else {
          BIT_CLEAR(rab_slice_req->flags_drv, RAB_FLAGS_DRV_FIXED);
        }

        if (pulp_rab_slice_check(rab_slice_req)) // free slice
          pulp_rab_slice_free(rab_config, rab_slice_req);
      }
    }
  }

  // for debugging
  //pulp_rab_mapping_print(rab_config,0xAAAA);

#if PLATFORM != ZEDBOARD
  // free L2TLB
  pulp_rab_l2_invalidate_all_entries(rab_config, 1);
#endif

  return;
}
// }}}

// free_striped {{{
void pulp_rab_free_striped(void *rab_config, unsigned long arg)
{
  int i, j;
  unsigned char id;

  // needed for RAB management
  RabSliceReq rab_slice_request;
  RabSliceReq *rab_slice_req = &rab_slice_request;

  // needed for RAB striping
  RabStripeElem *rab_stripe_elem;

#ifdef PROFILE_RAB_STR
  // reset the host clock counter
  host_reset_clock_counter();
#endif

  // get id/rab_mapping
  id = (unsigned char)arg;
  rab_slice_req->rab_port = 1;
  rab_slice_req->rab_mapping = id % RAB_L1_N_MAPPINGS_PORT_1;

  if (DEBUG_LEVEL_RAB_STR > 1) {
    printk(KERN_INFO "PULP - RAB: id = %d, n_elements = %d\n", id, rab_stripe_req[rab_slice_req->rab_mapping].n_elements);
  }

  if (rab_stripe_req[rab_slice_req->rab_mapping].n_elements > 0) {
    rab_stripe_elem = rab_stripe_req[rab_slice_req->rab_mapping].elements;

    // process every data element independently
    for (i = 0; i < rab_stripe_req[rab_slice_req->rab_mapping].n_elements; i++) {
      if (DEBUG_LEVEL_RAB_STR > 1) {
        printk(KERN_INFO "PULP - RAB: Element %d:\n", i);
      }

      rab_slice_req->flags_hw = rab_stripe_elem[i].flags_hw;

      // free the slices
      for (j = 0; j < rab_stripe_elem[i].n_slices; j++) {
        rab_slice_req->rab_slice = rab_stripe_elem[i].slice_idxs[j];

        // unlock and release pages when freeing the last slice
        rab_slice_req->flags_drv = 0;
        if (j < (rab_stripe_elem[i].n_slices - 1))
          BIT_SET(rab_slice_req->flags_drv, RAB_FLAGS_DRV_STRIPED);

        pulp_rab_slice_free(rab_config, rab_slice_req);
      }

      // free memory
      kfree(rab_stripe_elem[i].slice_idxs);
      for (j = 0; j < rab_stripe_elem[i].n_stripes; j++) {
        kfree(rab_stripe_elem[i].stripes[j].slice_configs);
      }
      kfree(rab_stripe_elem[i].stripes);
    }

    // free memory
    kfree(rab_stripe_req[rab_slice_req->rab_mapping].elements);

    // mark the stripe request as freed
    rab_stripe_req[rab_slice_req->rab_mapping].n_elements = 0;
  }

#ifdef PROFILE_RAB_STR
  // read the host clock counter
  host_clk_cntr_value = host_get_clock_counter();
  n_cyc_cleanup = host_clk_cntr_value;
  n_cyc_tot_cleanup += n_cyc_cleanup;

  n_cleanups++;

  // write the counter values to the buffers
  n_cyc_buf_cleanup[idx_buf_cleanup] = n_cyc_cleanup;
  idx_buf_cleanup++;

  // check for buffer overflow
  if (idx_buf_cleanup > PROFILE_RAB_N_REQUESTS) {
    idx_buf_cleanup = 0;
    printk(KERN_WARNING "PULP - RAB: n_cyc_buf_cleanup overflow!\n");
  }
#endif

  return;
}
// }}}

// }}}

// SoC Miss Handling {{{
/***********************************************************************************
 *
 * ███████╗ ██████╗  ██████╗    ███╗   ███╗██╗  ██╗
 * ██╔════╝██╔═══██╗██╔════╝    ████╗ ████║██║  ██║
 * ███████╗██║   ██║██║         ██╔████╔██║███████║
 * ╚════██║██║   ██║██║         ██║╚██╔╝██║██╔══██║
 * ███████║╚██████╔╝╚██████╗    ██║ ╚═╝ ██║██║  ██║
 * ╚══════╝ ╚═════╝  ╚═════╝    ╚═╝     ╚═╝╚═╝  ╚═╝
 *
 ***********************************************************************************/

// soc_mh_ena {{{
static int soc_mh_ena_static_1st_level(void *const rab_config, RabSliceReq *const req, const unsigned long pgd_pa)
{
  unsigned ret;

  pulp_rab_page_ptrs_get_field(req);

  req->addr_start = PGD_BASE_ADDR;
  req->addr_end = req->addr_start + ((PTRS_PER_PGD * sizeof(pgd_t)) - 1);
  req->addr_offset = pgd_pa;

  ret = pulp_rab_slice_get(req);
  if (ret != 0) {
    printk(KERN_ERR "PULP RAB SoC MH Enable failed to get RAB slice!\n");
    return ret;
  }
  pulp_rab_slice_free(rab_config, req);

  printk(KERN_DEBUG "PULP RAB SoC MH slice %u request: start 0x%08x, end 0x%08x, off 0x%010lx\n", req->rab_slice,
         req->addr_start, req->addr_end, req->addr_offset);

  ret = pulp_rab_slice_setup(rab_config, req, NULL);
  if (ret != 0) {
    printk(KERN_ERR "PULP RAB SoC MH slice %u request failed!\n", req->rab_slice);
    return ret;
  }

  return 0;
}

#if PLATFORM == JUNO || PLATFORM == TE0808
static int soc_mh_ena_static_2nd_level(void *const rab_config, RabSliceReq *const req, const pgd_t *const pgd)
{
  unsigned i_pmd;
  unsigned pmd_va;
  unsigned ret;
  pmd_t pmd;

  #if DEBUG_LEVEL_RAB_MH > 0
  unsigned long long entry_pa, entry_kva, pmd_stat;

  for (i_pmd = 0; i_pmd < PTRS_PER_PGD; ++i_pmd) {
    entry_pa = (unsigned long long)((unsigned long long *)__pa(pgd) + pgd_index(PGDIR_SIZE * i_pmd));
    entry_kva = (unsigned long long)((unsigned long long *)pgd + pgd_index(PGDIR_SIZE * i_pmd));
    pmd_stat = (unsigned long long)*((unsigned long long *)entry_kva);
    if (pmd_stat & 0x3)
      printk(KERN_INFO "PGD Entry %d @ pa = %#llx (kva = %#llx): PMD @ pa %#llx (+ status)\n", i_pmd, entry_pa, entry_kva,
             pmd_stat);
  }
  #endif

  pmd_va = PGD_BASE_ADDR;
  for (i_pmd = 0; i_pmd < RAB_N_STATIC_2ND_LEVEL_SLICES; ++i_pmd) {
    pulp_rab_page_ptrs_get_field(req);

    req->addr_start = pmd_va;
    req->addr_end = req->addr_start + ((PTRS_PER_PMD << 3) - 1);

    pmd_va = req->addr_end + 1;

    // dereference incremented kva to get pa of pmd
    pmd.pmd = (pmdval_t) * ((unsigned long *)pgd + pgd_index(PGDIR_SIZE * i_pmd));

    if (pmd_none(pmd) || pmd_bad(pmd))
      continue;

    pmd.pmd &= PAGE_MASK;

    req->addr_offset = pmd_val(pmd);

    ret = pulp_rab_slice_get(req);
    if (ret != 0) {
      printk(KERN_ERR "PULP RAB SoC MH Enable failed to get RAB slice!\n");
      return ret;
    }
    pulp_rab_slice_free(rab_config, req);

    printk(KERN_DEBUG "PULP RAB SoC MH slice %u request: start 0x%08x, end 0x%08x, off 0x%010lx\n", req->rab_slice,
           req->addr_start, req->addr_end, req->addr_offset);

    ret = pulp_rab_slice_setup(rab_config, req, NULL);
    if (ret != 0) {
      printk(KERN_ERR "PULP RAB SoC MH slice %u request failed!\n", req->rab_slice);
      return ret;
    }
  }

  return 0;
}
#endif

static unsigned static_2nd_lvl_slices_are_supported(void)
{
#if PLATFORM == JUNO || PLATFORM == TE0808
  return 1;
#else
  return 0;
#endif
}

/**
 * Check if there are no static slices among those not reserved for the host and free all other
 * slices.
 *
 * @rab_config: kernel virtual address of the RAB configuration port
 *
 * @return  1 if all RAB slices not reserved to the host have been freed; 0 if at least one slice
 *          has not yet expired.
 */
static unsigned rab_is_ready_for_soc_mh(void *const rab_config)
{
  RabSliceReq req;
  unsigned i;

  /**
   * Setting `date_cur` to `RAB_MAX_DATE_MH` will free all slices set up by the driver and the
   * runtime except if they are required to persist until the end of the application (so called
   * "static" slices).  `pulp_rab_slice_free()` will thus succeed for all except static slices.
   */
  req.date_cur = RAB_MAX_DATE_MH;
  req.rab_mapping = 0;
  req.rab_port = 1;

  for (i = rab_n_slices_reserved_for_host; i < RAB_L1_N_SLICES_PORT_1; ++i) {
    req.rab_slice = i;
    if (pulp_rab_slice_check(&req))
      pulp_rab_slice_free(rab_config, &req);
    else
      return 0;
  }

  return 1;
}

int pulp_rab_soc_mh_ena(void *const rab_config, unsigned static_2nd_lvl_slices)
{
  const pgd_t *pgd;
  unsigned long pgd_pa;
  RabSliceReq rab_slice_req;
  int retval;

  if (rab_soc_mh_is_ena == 1) {
    printk(KERN_WARNING "PULP RAB: Not enabling SoC MH because it is already enabled.\n");
    return -EALREADY;
  }

  if (static_2nd_lvl_slices && !static_2nd_lvl_slices_are_supported()) {
    printk(KERN_WARNING "PULP RAB: Static second-level slices are unsupported on your platform!\n");
    printk(KERN_WARNING "PULP RAB: Falling back to one static first-level slice.\n");
    static_2nd_lvl_slices = 0;
  }

  pgd = (const pgd_t *)current->mm->pgd;

  /**
   * Determine the physical address of the Page Global Directory (i.e., the process-specific
   * top-level page table).
   */
  pgd_pa = ((unsigned long)__pa(pgd));
  printk(KERN_DEBUG "PULP RAB SoC MH PGD PA: 0x%010lx\n", pgd_pa);

  /**
   * Initialize the RAB slice with basic properties that are the same for all slices.
   */
  rab_slice_req.date_cur = RAB_MAX_DATE;
  rab_slice_req.date_exp = RAB_MAX_DATE;
  rab_slice_req.page_idx_start = 0;
  rab_slice_req.page_idx_end = 0;
  rab_slice_req.rab_port = 1;
  rab_slice_req.rab_mapping = 0;
  // not setup in every mapping, not striped, constant
  rab_slice_req.flags_drv = 0;
  BIT_SET(rab_slice_req.flags_drv, RAB_FLAGS_DRV_CONST);
  // cache-coherent, disable write, enable read, valid
  rab_slice_req.flags_hw = 0;
  BIT_SET(rab_slice_req.flags_hw, RAB_FLAGS_HW_CC | RAB_FLAGS_HW_READ | RAB_FLAGS_HW_EN);

  /**
   * Even if the SoC manages the RAB, the first few slices remain reserved for the host, namely:
   *  - the first slice containing the mapping to contiguous L3, and
   *  - the next N slices containing the mapings to the entry level(s) of the page table (the value
   *    of N depends on whether first- or second-level slices are mapped statically).
   */
  rab_n_slices_reserved_for_host = 1;
#if PLATFORM == JUNO || PLATFORM == TE0808
  rab_n_slices_reserved_for_host += (static_2nd_lvl_slices ? RAB_N_STATIC_2ND_LEVEL_SLICES : 1);
#elif PLATFORM == ARIANE
  // one extra slice for rab config via host mapping
  rab_n_slices_reserved_for_host += 2;
#else
  rab_n_slices_reserved_for_host += 1;
#endif

  if (!rab_is_ready_for_soc_mh(rab_config)) {
    printk(KERN_ERR "PULP RAB: RAB is not ready to enable the SoC Miss Handler!\n");
    return -EBUSY;
  }

  /**
   * Set up RAB slices either for the first-level page table or for the second-level page tables.
   * If this fails, the SoC cannot handle RAB misses because it cannot access the page table
   * hierarchy in memory.
   */
  rab_soc_mh_is_ena = 1;
#if PLATFORM == JUNO || PLATFORM == TE0808
  if (static_2nd_lvl_slices)
    retval = soc_mh_ena_static_2nd_level(rab_config, &rab_slice_req, pgd);
  else
#endif
    retval = soc_mh_ena_static_1st_level(rab_config, &rab_slice_req, pgd_pa);

  if (retval != 0) {
    char level[255];
    if (static_2nd_lvl_slices)
      strcpy(level, "second");
    else
      strcpy(level, "first");
    printk(KERN_ERR "PULP RAB: Failed to configure slices for %s level of page table!\n", level);
    rab_soc_mh_is_ena = 0;
    return retval;
  }

  /**
   * The SoC now has access to the page table hierarchy in memory and will handle all RAB misses.
   * This Kernel driver must no longer handle these misses.
   */
  pulp_rab_mh_dis();

  return 0;
}
// }}}

// soc_mh_dis {{{
int pulp_rab_soc_mh_dis(void *const rab_config)
{
  unsigned i;
  RabSliceReq req;

  if (rab_soc_mh_is_ena == 0) {
    return -EALREADY;
  }

  /**
   * To make sure that the SoC can no longer access the page table hierarchy, we free all slices
   * used to map the initial levels of the page table.
   */
  req.rab_port = 1;
  req.rab_mapping = 0;
  req.flags_drv = 0;
  BIT_SET(req.flags_drv, RAB_FLAGS_DRV_CONST);
  for (i = 1; i < rab_n_slices_reserved_for_host; ++i) {
    req.rab_slice = i;
    pulp_rab_slice_free(rab_config, &req);
  }

  rab_n_slices_reserved_for_host = RAB_L1_N_SLICES_PORT_1;
  rab_soc_mh_is_ena = 0;

  return 0;
}
// }}}

// }}}

// Host Miss Handling {{{
/***********************************************************************************
 *
 * ██╗  ██╗ ██████╗ ███████╗████████╗    ███╗   ███╗██╗  ██╗
 * ██║  ██║██╔═══██╗██╔════╝╚══██╔══╝    ████╗ ████║██║  ██║
 * ███████║██║   ██║███████╗   ██║       ██╔████╔██║███████║
 * ██╔══██║██║   ██║╚════██║   ██║       ██║╚██╔╝██║██╔══██║
 * ██║  ██║╚██████╔╝███████║   ██║       ██║ ╚═╝ ██║██║  ██║
 * ╚═╝  ╚═╝ ╚═════╝ ╚══════╝   ╚═╝       ╚═╝     ╚═╝╚═╝  ╚═╝
 *
 ***********************************************************************************/

// mh_ena {{{
long pulp_rab_mh_ena(void *rab_config, unsigned int mh_acp, unsigned int mh_lvl)
{
  // check if miss handling is not already enabled, i.e., if workqueue already exists
  // for example because the clean up failed
  if (rab_mh_wq)
    pulp_rab_mh_dis();

  rab_mh_acp = mh_acp;
  rab_mh_lvl = mh_lvl;

  // create workqueue for RAB miss handling - single-threaded workqueue for strict ordering
  rab_mh_wq = alloc_workqueue("%s", WQ_UNBOUND | WQ_HIGHPRI, 1, rab_mh_wq_name);
  if (rab_mh_wq == NULL) {
    printk(KERN_WARNING "PULP: Allocation of workqueue for host RAB miss handling failed.\n");
    return -ENOMEM;
  }
  // initialize the workqueue
  INIT_WORK(&rab_mh_w, (void *)pulp_rab_handle_miss);

  // register information of the calling user-space process
  user_task = current;
  user_mm = current->mm;

  // enable - protect with semaphore?
  rab_mh = 1;
  rab_mh_date = 1;

  printk(KERN_INFO "PULP: Host RAB miss handling enabled.\n");

  return 0;
}
// }}}

// mh_dis {{{
void pulp_rab_mh_dis(void)
{
  // disable - protect with semaphore?
  rab_mh = 0;
  rab_mh_date = 0;

  if (rab_mh_wq) {
    // Flush and destroy the workqueue, and reset workqueue pointer to default value.
    destroy_workqueue(rab_mh_wq);
    rab_mh_wq = 0;

    printk(KERN_INFO "PULP: Host RAB miss handling disabled.\n");
  }

  return;
}
// }}}

// mh_sched {{{
unsigned pulp_rab_mh_sched(void)
{
  if (rab_mh) {
#ifdef PROFILE_RAB_MH
    // read timer
    n_cyc_response_tmp = ioread32((void *)((unsigned long)(pulp->clusters) + TIMER_GET_TIME_LO_OFFSET_B));
#endif
    schedule_work(&rab_mh_w);
  } else if (!rab_soc_mh_is_ena)
    pulp_rab_mapping_print(pulp->rab_config, 0xAAAA);

  return rab_mh;
}
// }}}

// handle_miss {{{
void pulp_rab_handle_miss(unsigned unused)
{
  int err, i, j, handled, result;
  unsigned meta, id_pe, id_cluster, axuser;
  unsigned addr_start;
  unsigned long addr_phys;

  // what get_user_pages needs
  unsigned long start;
  struct page **pages;
  unsigned write;

  // needed for RAB management
  RabSliceReq rab_slice_request;
  RabSliceReq *rab_slice_req = &rab_slice_request;

  // needed for L2 TLB
  L2Entry l2_entry_request;
  L2Entry *l2_entry = &l2_entry_request;
  int use_l1 = 1;
  int err_l2 = 0;

  if (DEBUG_LEVEL_RAB_MH > 1)
    printk(KERN_INFO "PULP: RAB miss handling routine started.\n");

#ifdef PROFILE_RAB_MH_SIMPLE
  n_schedule++;
#endif

  // empty miss-handling FIFOs
  for (i = 0; i < RAB_MH_FIFO_DEPTH; i++) {
    // read ID first for empty FIFO detection
    rab_mh_meta[i] = IOREAD_L((void *)((unsigned long)(pulp->rab_config) + RAB_MH_META_FIFO_OFFSET_B));

    // detect empty FIFOs -> end routine
    if (rab_mh_meta[i] & 0x80000000)
      break;

    // read valid addr
    rab_mh_addr[i] = IOREAD_L((void *)((unsigned long)(pulp->rab_config) + RAB_MH_ADDR_FIFO_OFFSET_B));

    // handle every miss separately
    err = 0;
    addr_start = rab_mh_addr[i];
    meta = rab_mh_meta[i];

    // check the ID
    id_pe = BF_GET(meta, 0, AXI_ID_WIDTH_CORE);
    id_cluster = BF_GET(meta, AXI_ID_WIDTH_CLUSTER + AXI_ID_WIDTH_CORE, AXI_ID_WIDTH_SOC);
    axuser = BF_GET(meta, AXI_ID_WIDTH + 1, AXI_USER_WIDTH);
    // - 0x3;
    //id_cluster = BF_GET(id, AXI_ID_WIDTH_CORE, AXI_ID_WIDTH_CLUSTER) - 0x2;

    if ((DEBUG_LEVEL_RAB_MH > 0)) { //} || (i > 0)) {
      printk(KERN_INFO "PULP: RAB miss - i = %2d, date = %#3x, id_pe = %#3x, axuser = %#2x, addr = %#8x\n", i, rab_mh_date,
             id_pe, axuser, rab_mh_addr[i]);
    }

    // identify RAB port - for now, only handle misses on Port 1: PULP -> Host
    if (BF_GET(meta, AXI_ID_WIDTH, 1))
      rab_slice_req->rab_port = 1;
    else {
      printk(KERN_WARNING "PULP: Cannot handle RAB miss on ports different from Port 1.\n");
      printk(KERN_WARNING "PULP: RAB miss - meta = %#5x, addr = %#8x\n", rab_mh_meta[i], rab_mh_addr[i]);
      continue;
    }

    // only handle misses from PEs' data interfaces
    if ((BF_GET(meta, AXI_ID_WIDTH_CORE, AXI_ID_WIDTH_CLUSTER) != 0x2) ||
        ((id_cluster < 0) || (id_cluster > (N_CLUSTERS - 1))) || ((id_pe < 0) || (id_pe > N_CORES - 1))) {
      printk(KERN_WARNING
             "PULP: Can only handle RAB misses originating from PE's data interfaces. meta = %#x | addr = %#x\n",
             rab_mh_meta[i], rab_mh_addr[i]);
      // for debugging
      //   pulp_rab_mapping_print(pulp->rab_config,0xAAAA);

      continue;
    }

#ifdef PROFILE_RAB_MH
    // read the timer
    n_cyc_schedule = ioread32((void *)((unsigned long)(pulp->clusters) + TIMER_GET_TIME_LO_OFFSET_B));
    n_cyc_tot_schedule += n_cyc_schedule;

    // save resp_tmp
    n_cyc_response = n_cyc_response_tmp;
    n_cyc_tot_response += n_cyc_response;

    n_misses++;
#endif
#ifdef PROFILE_RAB_MH_SIMPLE
    n_misses++;
#endif

    // check if there has been a miss to the same page before
    handled = 0;
    for (j = 0; j < i; j++) {
      if ((addr_start & BF_MASK_GEN(PAGE_SHIFT, sizeof(unsigned) * 8 - PAGE_SHIFT)) ==
          (rab_mh_addr[j] & BF_MASK_GEN(PAGE_SHIFT, sizeof(unsigned) * 8 - PAGE_SHIFT))) {
        handled = 1;
        if (DEBUG_LEVEL_RAB_MH > 0) {
          printk(KERN_WARNING "PULP: Already handled a miss to this page.\n");
          printk(KERN_INFO "PULP: RAB miss - j = %2d,        %#3x, id_pe = %#3lx, axuser = %#2lx, addr = %#8x\n", j,
                 rab_mh_date, BF_GET(rab_mh_meta[j], 0, AXI_ID_WIDTH_CORE),
                 BF_GET(rab_mh_meta[j], AXI_ID_WIDTH + 1, AXI_USER_WIDTH), rab_mh_addr[j]);
          printk(KERN_INFO "PULP: RAB miss - i = %2d, date = %#3x, id_pe = %#3lx, axuser = %#2lx, addr = %#8x\n", i,
                 rab_mh_date, BF_GET(rab_mh_meta[i], 0, AXI_ID_WIDTH_CORE),
                 BF_GET(rab_mh_meta[i], AXI_ID_WIDTH + 1, AXI_USER_WIDTH), rab_mh_addr[i]);
          // for debugging only - deactivate fetch enable
          // iowrite32(0xC0000000,(void *)((unsigned long)(pulp->gpio)+0x8));
        }
        break;
      }
    }

    // handle a miss
    if (!handled) {
#ifdef PROFILE_RAB_MH
      // reset the host clock counter
      host_reset_clock_counter();

      // read the host clock counter
      host_clk_cntr_value = host_get_clock_counter();

      n_first_misses++;
#endif
#ifdef PROFILE_RAB_MH_SIMPLE
      n_first_misses++;
#endif

      if (DEBUG_LEVEL_RAB_MH > 1) {
        printk(KERN_INFO "PULP: Trying to handle RAB miss to user-space virtual address %#x.\n", addr_start);
      }

      // what get_user_pages returns
      pages = (struct page **)kmalloc((size_t)(sizeof(struct page *)), GFP_KERNEL);
      if (pages == NULL) {
        printk(KERN_WARNING "PULP: Memory allocation failed.\n");
        err = 1;
        goto miss_handling_error;
      }

      // align address to page border / 4kB
      start = (unsigned long)(addr_start)&BF_MASK_GEN(PAGE_SHIFT, sizeof(unsigned long) * 8 - PAGE_SHIFT);

      // get pointer to user-space buffer and lock it into memory, get a single page
      // try read/write mode first - fall back to read only
      write = 1;
      down_read(&user_task->mm->mmap_sem);
#if LINUX_VERSION_CODE <= KERNEL_VERSION(4, 13, 0)
      result = get_user_pages_remote(user_task, user_task->mm, start, 1, write ? FOLL_WRITE : 0, pages, NULL);
#else
      result = get_user_pages_remote(user_task, user_task->mm, start, 1, write ? FOLL_WRITE : 0, pages, NULL, NULL);
#endif
      if (result == -EFAULT) {
        write = 0;
#if LINUX_VERSION_CODE <= KERNEL_VERSION(4, 13, 0)
        result = get_user_pages_remote(user_task, user_task->mm, start, 1, write ? FOLL_WRITE : 0, pages, NULL);
#else
        result = get_user_pages_remote(user_task, user_task->mm, start, 1, write ? FOLL_WRITE : 0, pages, NULL, NULL);
#endif
      }
      up_read(&user_task->mm->mmap_sem);
      //current->mm = user_task->mm;
      //result = get_user_pages_fast(start, 1, 1, pages);
      if (result != 1) {
        printk(KERN_WARNING "PULP: Could not get requested user-space virtual address %#x.\n", addr_start);
        err = 1;
        goto miss_handling_error;
      }

      // virtual-to-physical address translation
      addr_phys = (unsigned long)page_to_phys(pages[0]);
      if (DEBUG_LEVEL_MEM > 1) {
        printk(KERN_INFO "PULP: Physical address = %#lx\n", addr_phys);
      }

#ifdef PROFILE_RAB_MH
      host_clk_cntr_value_start = host_clk_cntr_value;

      // read the host clock counter
      host_clk_cntr_value = host_get_clock_counter();
      n_cyc_get_user_pages = host_clk_cntr_value - host_clk_cntr_value_start;
      n_cyc_tot_get_user_pages += n_cyc_get_user_pages;
#endif

      // fill rab_slice_req structure
      // allocate a fixed number of slices to each PE???
      // works for one port only!!!
      rab_slice_req->date_cur = (unsigned char)rab_mh_date;
      rab_slice_req->date_exp = (unsigned char)rab_mh_date;
      rab_slice_req->page_idx_start = 0;
      rab_slice_req->page_idx_end = 0;
      rab_slice_req->rab_mapping = (unsigned)pulp_rab_mapping_get_active();
      rab_slice_req->flags_drv = 0;

      rab_slice_req->addr_start = (unsigned)start;
      rab_slice_req->addr_end = (unsigned)start + PAGE_SIZE;
      rab_slice_req->addr_offset = addr_phys;
      rab_slice_req->flags_hw = 0;
      BIT_SET(rab_slice_req->flags_hw, RAB_FLAGS_HW_READ | RAB_FLAGS_HW_EN);
      if (write)
        BIT_SET(rab_slice_req->flags_hw, RAB_FLAGS_HW_WRITE);
      if (rab_mh_acp)
        BIT_SET(rab_slice_req->flags_hw, RAB_FLAGS_HW_CC);

      // Check which TLB level to use.
      // If rab_mh_lvl is 0, enter the entry in L1 if free slice is available. If not, enter in L2.
      if (rab_mh_lvl == 2) {
        use_l1 = 0;
      } else {
        // get a free slice
        use_l1 = 1;
        err = pulp_rab_slice_get(rab_slice_req);
        if (err) {
          if (rab_mh_lvl == 1) {
            printk(KERN_WARNING "PULP: RAB miss handling error 2.\n");
            goto miss_handling_error;
          } else
            use_l1 = 0;
        }
      }
      err = 0;
      if (use_l1 == 0) { // Use L2
        l2_entry->flags = rab_slice_req->flags_hw;
        l2_entry->pfn_v = (unsigned)(start >> PAGE_SHIFT);
        l2_entry->pfn_p = (unsigned)(addr_phys >> PAGE_SHIFT);
        l2_entry->page_ptr = pages[0];
        err_l2 = pulp_rab_l2_setup_entry(pulp->rab_config, l2_entry, rab_slice_req->rab_port, 1);
      } else { // Use L1
        // free memory of slices to be re-configured
        pulp_rab_slice_free(pulp->rab_config, rab_slice_req);

        // check for free field in page_ptrs list
        err = pulp_rab_page_ptrs_get_field(rab_slice_req);
        if (err) {
          printk(KERN_WARNING "PULP: RAB miss handling error 0.\n");
          goto miss_handling_error;
        }

        // setup slice
        err = pulp_rab_slice_setup(pulp->rab_config, rab_slice_req, pages);
        if (err) {
          printk(KERN_WARNING "PULP: RAB miss handling error 1.\n");
          goto miss_handling_error;
        }
      } // if (use_l1 == 0)

#ifdef PROFILE_RAB_MH
      host_clk_cntr_value_start = host_clk_cntr_value;

      // read the host clock counter
      host_clk_cntr_value = host_get_clock_counter();
      n_cyc_setup = host_clk_cntr_value - host_clk_cntr_value_start;
      n_cyc_tot_setup += n_cyc_setup;
#endif

      // flush the entire page from the caches if ACP is not used
      if (!rab_mh_acp)
        pulp_mem_cache_flush(pages[0], 0, PAGE_SIZE);

      if (use_l1 == 0)
        kfree(pages);

      if (rab_mh_lvl == 1)
        if (rab_slice_req->rab_slice == (RAB_L1_N_SLICES_PORT_1 - 1)) {
          rab_mh_date++;
          if (rab_mh_date > RAB_MAX_DATE_MH)
            rab_mh_date = 0;
          //printk(KERN_INFO "rab_mh_date = %d\n",rab_mh_date);
        }

#ifdef PROFILE_RAB_MH
      host_clk_cntr_value_start = host_clk_cntr_value;

      // read the host clock counter
      host_clk_cntr_value = host_get_clock_counter();
      n_cyc_cache_flush = host_clk_cntr_value - host_clk_cntr_value_start;
      n_cyc_tot_cache_flush += n_cyc_cache_flush;
#endif
    }

    // // for debugging
    // pulp_rab_mapping_print(pulp->rab_config,0xAAAA);

    if (!axuser) {
      iowrite32(BIT_N_SET(id_pe),
                (void *)((unsigned long)(pulp->clusters) + CLUSTER_SIZE_B * id_cluster + CLUSTER_PERIPHERALS_OFFSET_B +
                         BBMUX_CLKGATE_OFFSET_B + EU_SW_EVENTS_OFFSET_B + RAB_WAKEUP_OFFSET_B));
    }

    /*
     * printk(KERN_INFO "WAKEUP: value = %#x, address = %#x\n",BIT_N_SET(id_pe), \
     *   CLUSTER_SIZE_B*id_cluster + CLUSTER_PERIPHERALS_OFFSET_B + BBMUX_CLKGATE_OFFSET_B
     *   + EU_SW_EVENTS_OFFSET_B + RAB_WAKEUP_OFFSET_B);
     */

#ifdef PROFILE_RAB_MH
    // read the timer
    n_cyc_update = ioread32((void *)((unsigned long)(pulp->clusters) + TIMER_GET_TIME_LO_OFFSET_B));
    n_cyc_tot_update += n_cyc_update;

    // write the counter values to the buffers
    n_cyc_buf_response[idx_buf_response] = n_cyc_response;
    idx_buf_response++;
    n_cyc_buf_schedule[idx_buf_schedule] = n_cyc_schedule;
    idx_buf_schedule++;
    n_cyc_buf_get_user_pages[idx_buf_get_user_pages] = n_cyc_get_user_pages;
    idx_buf_get_user_pages++;
    n_cyc_buf_setup[idx_buf_setup] = n_cyc_setup;
    idx_buf_setup++;
    n_cyc_buf_cache_flush[idx_buf_cache_flush] = n_cyc_cache_flush;
    idx_buf_cache_flush++;
    n_cyc_buf_update[idx_buf_update] = n_cyc_update;
    idx_buf_update++;

    // check for buffer overflow
    if (idx_buf_response > PROFILE_RAB_N_UPDATES) {
      idx_buf_response = 0;
      printk(KERN_WARNING "PULP - RAB: n_cyc_buf_response overflow!\n");
    }
    if (idx_buf_schedule > PROFILE_RAB_N_UPDATES) {
      idx_buf_schedule = 0;
      printk(KERN_WARNING "PULP - RAB: n_cyc_buf_schedule overflow!\n");
    }
    if (idx_buf_get_user_pages > PROFILE_RAB_N_ELEMENTS) {
      idx_buf_get_user_pages = 0;
      printk(KERN_WARNING "PULP - RAB: n_cyc_buf_get_user_pages overflow!\n");
    }
    if (idx_buf_setup > PROFILE_RAB_N_REQUESTS) {
      idx_buf_setup = 0;
      printk(KERN_WARNING "PULP - RAB: n_cyc_buf_setup overflow!\n");
    }
    if (idx_buf_cache_flush > PROFILE_RAB_N_ELEMENTS) {
      idx_buf_cache_flush = 0;
      printk(KERN_WARNING "PULP - RAB: n_cyc_buf_cache_flush overflow!\n");
    }
    if (idx_buf_update > PROFILE_RAB_N_UPDATES) {
      idx_buf_update = 0;
      printk(KERN_WARNING "PULP - RAB: n_cyc_buf_update overflow!\n");
    }

    // update accumulators in shared memory
    iowrite32(n_cyc_tot_response, (void *)((unsigned long)(pulp->l3_mem) + N_CYC_TOT_RESPONSE_OFFSET_B));
    iowrite32(n_cyc_tot_update, (void *)((unsigned long)(pulp->l3_mem) + N_CYC_TOT_UPDATE_OFFSET_B));
    iowrite32(n_cyc_tot_setup, (void *)((unsigned long)(pulp->l3_mem) + N_CYC_TOT_SETUP_OFFSET_B));
    iowrite32(n_cyc_tot_cache_flush, (void *)((unsigned long)(pulp->l3_mem) + N_CYC_TOT_CACHE_FLUSH_OFFSET_B));
    iowrite32(n_cyc_tot_get_user_pages, (void *)((unsigned long)(pulp->l3_mem) + N_CYC_TOT_GET_USER_PAGES_OFFSET_B));
    iowrite32(n_cyc_tot_schedule, (void *)((unsigned long)(pulp->l3_mem) + N_CYC_TOT_SCHEDULE_OFFSET_B));
    iowrite32(n_first_misses, (void *)((unsigned long)(pulp->l3_mem) + N_FIRST_MISSES_OFFSET_B));
    iowrite32(n_misses, (void *)((unsigned long)(pulp->l3_mem) + N_MISSES_OFFSET_B));

#endif
  // error handling
  miss_handling_error:
    if (err) {
      printk(KERN_WARNING "PULP: Cannot handle RAB miss: id = %#x, addr = %#x\n", rab_mh_meta[i], rab_mh_addr[i]);

      // for debugging
      pulp_rab_mapping_print(pulp->rab_config, 0xAAAA);
    }

  } // for i<RAB_MH_FIFO_DEPTH

  if (DEBUG_LEVEL_RAB_MH > 1)
    printk(KERN_INFO "PULP: RAB miss handling routine finished.\n");

  if (i > (RAB_MH_FIFO_DEPTH / 4 * 3))
    printk(KERN_WARNING "PULP: RAB MH FIFO almost full. Fill level was %d/%d\n", i, RAB_MH_FIFO_DEPTH);

  return;
}
// }}}

// }}}

// AX Logger {{{
#if RAB_AX_LOG_EN == 1
/***********************************************************************************
   *
   *  █████╗ ██╗  ██╗    ██╗      ██████╗  ██████╗
   * ██╔══██╗╚██╗██╔╝    ██║     ██╔═══██╗██╔════╝
   * ███████║ ╚███╔╝     ██║     ██║   ██║██║  ███╗
   * ██╔══██║ ██╔██╗     ██║     ██║   ██║██║   ██║
   * ██║  ██║██╔╝ ██╗    ███████╗╚██████╔╝╚██████╔╝
   * ╚═╝  ╚═╝╚═╝  ╚═╝    ╚══════╝ ╚═════╝  ╚═════╝
   *
   ***********************************************************************************/

// ax_log_init {{{
int pulp_rab_ax_log_init(void)
{
  unsigned gpio, ready, status;

  // allocate memory for the log buffers
  rab_ar_log_buf = (unsigned *)vmalloc(RAB_AX_LOG_BUF_SIZE_B);
  rab_aw_log_buf = (unsigned *)vmalloc(RAB_AX_LOG_BUF_SIZE_B);
  rab_cfg_log_buf = (unsigned *)vmalloc(RAB_AX_LOG_BUF_SIZE_B);
  if ((rab_ar_log_buf == NULL) || (rab_aw_log_buf == NULL) || (rab_cfg_log_buf == NULL)) {
    printk(KERN_WARNING "PULP: Could not allocate kernel memory for RAB AX log buffer.\n");
    return -ENOMEM;
  }

  // initialize indices
  rab_ar_log_buf_idx = 0;
  rab_aw_log_buf_idx = 0;
  rab_cfg_log_buf_idx = 0;

  // clear AX log
  gpio = 0;
  BIT_SET(gpio, BF_MASK_GEN(GPIO_RST_N, 1));
  BIT_SET(gpio, BF_MASK_GEN(GPIO_CLK_EN, 1));
  BIT_SET(gpio, BF_MASK_GEN(GPIO_RAB_AR_LOG_CLR, 1));
  BIT_SET(gpio, BF_MASK_GEN(GPIO_RAB_AW_LOG_CLR, 1));
  #if PLATFORM == JUNO
  BIT_SET(gpio, BF_MASK_GEN(GPIO_RAB_CFG_LOG_CLR, 1));
  #endif
  iowrite32(gpio, (void *)((unsigned long)(pulp->gpio) + 0x8));

  // wait for ready
  ready = 0;
  while (!ready) {
    udelay(25);
    status = ioread32((void *)((unsigned long)pulp->gpio));
    ready = BF_GET(status, GPIO_RAB_AR_LOG_RDY, 1) && BF_GET(status, GPIO_RAB_AW_LOG_RDY, 1);
  #if PLATFORM == JUNO
    ready = ready && BF_GET(status, GPIO_RAB_CFG_LOG_RDY, 1);
  #endif
  }

  // remove the AX log clear
  BIT_CLEAR(gpio, BF_MASK_GEN(GPIO_RAB_AR_LOG_CLR, 1));
  BIT_CLEAR(gpio, BF_MASK_GEN(GPIO_RAB_AW_LOG_CLR, 1));
  #if PLATFORM == JUNO
  BIT_CLEAR(gpio, BF_MASK_GEN(GPIO_RAB_CFG_LOG_CLR, 1));
  #endif
  iowrite32(gpio, (void *)((unsigned long)(pulp->gpio) + 0x8));

  return 0;
}
// }}}

// ax_log_free {{{
void pulp_rab_ax_log_free(void)
{
  vfree(rab_ar_log_buf);
  vfree(rab_aw_log_buf);
  vfree(rab_cfg_log_buf);

  return;
}
// }}}

// ax_log_read {{{
void pulp_rab_ax_log_read(unsigned gpio_value, unsigned clear)
{
  unsigned i;
  unsigned addr, ts, meta;

  unsigned gpio;
  unsigned status, ready;

  gpio = gpio_value;

  // disable clocks
  if (clear) {
    BIT_CLEAR(gpio, BF_MASK_GEN(GPIO_CLK_EN, 1));
    iowrite32(gpio, (void *)((unsigned long)(pulp->gpio) + 0x8));
  }

  // read out AR log
  for (i = 0; i < (RAB_AX_LOG_SIZE_B / 4 / 3); i++) {
    ts = ioread32((void *)((unsigned long)(pulp->rab_ar_log) + (i * 3 + 0) * 4));
    meta = ioread32((void *)((unsigned long)(pulp->rab_ar_log) + (i * 3 + 1) * 4));
    addr = ioread32((void *)((unsigned long)(pulp->rab_ar_log) + (i * 3 + 2) * 4));

    if ((ts == 0) && (meta == 0) && (addr == 0))
      break;

    rab_ar_log_buf[rab_ar_log_buf_idx + 0] = ts;
    rab_ar_log_buf[rab_ar_log_buf_idx + 1] = meta;
    rab_ar_log_buf[rab_ar_log_buf_idx + 2] = addr;

    rab_ar_log_buf_idx += 3;

    if (rab_ar_log_buf_idx > (RAB_AX_LOG_BUF_SIZE_B / 4 / 3)) {
      rab_ar_log_buf_idx = 0;
      printk(KERN_WARNING "PULP - RAB: AR log buf overflow!\n");
    }
  }

  // read out AW log
  for (i = 0; i < (RAB_AX_LOG_SIZE_B / 4 / 3); i++) {
    ts = ioread32((void *)((unsigned long)(pulp->rab_aw_log) + (i * 3 + 0) * 4));
    meta = ioread32((void *)((unsigned long)(pulp->rab_aw_log) + (i * 3 + 1) * 4));
    addr = ioread32((void *)((unsigned long)(pulp->rab_aw_log) + (i * 3 + 2) * 4));

    if ((ts == 0) && (meta == 0) && (addr == 0))
      break;

    rab_aw_log_buf[rab_aw_log_buf_idx + 0] = ts;
    rab_aw_log_buf[rab_aw_log_buf_idx + 1] = meta;
    rab_aw_log_buf[rab_aw_log_buf_idx + 2] = addr;
    rab_aw_log_buf_idx += 3;

    if (rab_aw_log_buf_idx > (RAB_AX_LOG_BUF_SIZE_B / 4 / 3)) {
      rab_aw_log_buf_idx = 0;
      printk(KERN_WARNING "PULP - RAB: AW log buf overflow!\n");
    }
  }

  // read out CFG log
  #if PLATFORM == JUNO
  for (i = 0; i < (RAB_CFG_LOG_SIZE_B / 4 / 3); i++) {
    ts = ioread32((void *)((unsigned long)(pulp->rab_cfg_log) + (i * 3 + 0) * 4));
    meta = ioread32((void *)((unsigned long)(pulp->rab_cfg_log) + (i * 3 + 1) * 4));
    addr = ioread32((void *)((unsigned long)(pulp->rab_cfg_log) + (i * 3 + 2) * 4));

    if ((ts == 0) && (meta == 0) && (addr == 0))
      break;

    rab_cfg_log_buf[rab_cfg_log_buf_idx + 0] = ts;
    rab_cfg_log_buf[rab_cfg_log_buf_idx + 1] = meta;
    rab_cfg_log_buf[rab_cfg_log_buf_idx + 2] = addr;
    rab_cfg_log_buf_idx += 3;

    if (rab_cfg_log_buf_idx > (RAB_AX_LOG_BUF_SIZE_B / 4 / 3)) {
      rab_cfg_log_buf_idx = 0;
      printk(KERN_WARNING "PULP - RAB: CFG log buf overflow!\n");
    }
  }
  #endif

  // clear loggers and wait for ready
  if (clear) {
    BIT_SET(gpio, BF_MASK_GEN(GPIO_RAB_AR_LOG_CLR, 1));
    BIT_SET(gpio, BF_MASK_GEN(GPIO_RAB_AW_LOG_CLR, 1));
  #if PLATFORM == JUNO
    BIT_SET(gpio, BF_MASK_GEN(GPIO_RAB_CFG_LOG_CLR, 1));
  #endif
    iowrite32(gpio, (void *)((unsigned long)(pulp->gpio) + 0x8));

    ready = 0;
    while (!ready) {
      udelay(25);
      status = ioread32((void *)((unsigned long)pulp->gpio));
      ready = BF_GET(status, GPIO_RAB_AR_LOG_RDY, 1) && BF_GET(status, GPIO_RAB_AW_LOG_RDY, 1);
  #if PLATFORM == JUNO
      ready = ready && BF_GET(status, GPIO_RAB_CFG_LOG_RDY, 1);
  #endif
    }
    BIT_CLEAR(gpio, BF_MASK_GEN(GPIO_RAB_AR_LOG_CLR, 1));
    BIT_CLEAR(gpio, BF_MASK_GEN(GPIO_RAB_AW_LOG_CLR, 1));
  #if PLATFORM == JUNO
    BIT_CLEAR(gpio, BF_MASK_GEN(GPIO_RAB_CFG_LOG_CLR, 1));
  #endif
    iowrite32(gpio, (void *)((unsigned long)(pulp->gpio) + 0x8));

    // continue
    iowrite32(gpio_value, (void *)((unsigned long)(pulp->gpio) + 0x8));
  }

  return;
}
// }}}

// ax_log_print {{{
void pulp_rab_ax_log_print(void)
{
  unsigned i;
  unsigned addr, ts, meta;
  unsigned id, len;
  unsigned type;

  // read out and clear the AR log
  type = 0;
  for (i = 0; i < rab_ar_log_buf_idx; i = i + 3) {
    ts = rab_ar_log_buf[i + 0];
    meta = rab_ar_log_buf[i + 1];
    addr = rab_ar_log_buf[i + 2];

    len = BF_GET(meta, 0, 8);
    id = BF_GET(meta, 8, 10);

  #if RAB_AX_LOG_PRINT_FORMAT == 0 // DEBUG
    printk(KERN_INFO "AR Log: %u %#x %3u %#x %u\n", ts, addr, len, id, type);
  #else // 1 = MATLAB
    printk(KERN_INFO "AR Log: %u %u %u %u %u\n", ts, addr, len, id, type);
  #endif
  }
  rab_ar_log_buf_idx = 0;

  // read out and clear the AW log
  type = 1;
  for (i = 0; i < rab_aw_log_buf_idx; i = i + 3) {
    ts = rab_aw_log_buf[i + 0];
    meta = rab_aw_log_buf[i + 1];
    addr = rab_aw_log_buf[i + 2];

    len = BF_GET(meta, 0, 8);
    id = BF_GET(meta, 8, 10);

  #if RAB_AX_LOG_PRINT_FORMAT == 0 // DEBUG
    printk(KERN_INFO "AW Log: %u %#x %3u %#x %u\n", ts, addr, len, id, type);
  #else // 1 = MATLAB
    printk(KERN_INFO "AW Log: %u %u %u %u %u\n", ts, addr, len, id, type);
  #endif
  }
  rab_aw_log_buf_idx = 0;

  // read out and clear the CFG log
  type = 1;
  for (i = 0; i < rab_cfg_log_buf_idx; i = i + 3) {
    ts = rab_cfg_log_buf[i + 0];
    meta = rab_cfg_log_buf[i + 1];
    addr = rab_cfg_log_buf[i + 2];

    len = BF_GET(meta, 0, 8);
    id = BF_GET(meta, 8, 10);

  #if RAB_AX_LOG_PRINT_FORMAT == 0 // DEBUG
    printk(KERN_INFO "CFG Log: %u %#x %3u %#x %u\n", ts, addr, len, id, type);
  #else // 1 = MATLAB
    printk(KERN_INFO "CFG Log: %u %u %u %u %u\n", ts, addr, len, id, type);
  #endif
  }
  rab_cfg_log_buf_idx = 0;

  return;
}
// }}}

// ax_log_to_user {{{
void pulp_rab_ax_log_to_user(unsigned long arg)
{
  unsigned idxs[3];

  /**
     * We assume that the application that calls this function operates in a 32-bit address space.
     * Thus, all user-space pointers are 32 bit wide, while kernel-space pointers can be either 32
     * or 64 bit wide.
     */

  // to read from and write to user space
  uint32_t ptrs[4];
  unsigned long n_bytes_do, n_bytes_left;
  unsigned byte;

  // what we get from user space
  unsigned long status;
  unsigned long ar_log_buf_user;
  unsigned long aw_log_buf_user;
  unsigned long cfg_log_buf_user;

  // get the pointers - arg already checked above
  byte = 0;
  n_bytes_left = sizeof(ptrs);
  n_bytes_do = n_bytes_left;
  while (n_bytes_do > 0) {
    n_bytes_left = __copy_from_user((void *)((char *)ptrs + byte), (void __user *)((char *)arg + byte), n_bytes_do);
    byte += (n_bytes_do - n_bytes_left);
    n_bytes_do = n_bytes_left;
  }

  // extract addresses
  status = (unsigned long)ptrs[0];
  ar_log_buf_user = (unsigned long)ptrs[1];
  aw_log_buf_user = (unsigned long)ptrs[2];
  cfg_log_buf_user = (unsigned long)ptrs[3];

  // write AR log buffer
  byte = 0;
  n_bytes_left = rab_ar_log_buf_idx * 3 * sizeof(uint32_t);
  n_bytes_do = n_bytes_left;
  while (n_bytes_do > 0) {
    n_bytes_left =
      copy_to_user((void __user *)((char *)ar_log_buf_user + byte), (void *)((char *)rab_ar_log_buf + byte), n_bytes_do);
    byte += (n_bytes_do - n_bytes_left);
    n_bytes_do = n_bytes_left;
  }

  // write AW log buffer
  byte = 0;
  n_bytes_left = rab_aw_log_buf_idx * 3 * sizeof(uint32_t);
  n_bytes_do = n_bytes_left;
  while (n_bytes_do > 0) {
    n_bytes_left =
      copy_to_user((void __user *)((char *)aw_log_buf_user + byte), (void *)((char *)rab_aw_log_buf + byte), n_bytes_do);
    byte += (n_bytes_do - n_bytes_left);
    n_bytes_do = n_bytes_left;
  }

  // write CFG log buffer
  byte = 0;
  n_bytes_left = rab_cfg_log_buf_idx * 3 * sizeof(uint32_t);
  n_bytes_do = n_bytes_left;
  while (n_bytes_do > 0) {
    n_bytes_left =
      copy_to_user((void __user *)((char *)cfg_log_buf_user + byte), (void *)((char *)rab_cfg_log_buf + byte), n_bytes_do);
    byte += (n_bytes_do - n_bytes_left);
    n_bytes_do = n_bytes_left;
  }

  // write status
  idxs[0] = rab_ar_log_buf_idx;
  idxs[1] = rab_aw_log_buf_idx;
  idxs[2] = rab_cfg_log_buf_idx;
  byte = 0;
  n_bytes_left = sizeof(idxs);
  n_bytes_do = n_bytes_left;
  while (n_bytes_do > 0) {
    n_bytes_left = copy_to_user((void __user *)((char *)status + byte), (void *)((char *)idxs + byte), n_bytes_do);
    byte += (n_bytes_do - n_bytes_left);
    n_bytes_do = n_bytes_left;
  }

  // reset indices
  rab_ar_log_buf_idx = 0;
  rab_aw_log_buf_idx = 0;
  rab_cfg_log_buf_idx = 0;
}
#endif
// }}}

// Profiling {{{
#if defined(PROFILE_RAB_STR) || defined(PROFILE_RAB_MH)
/***********************************************************************************
   *
   * ██████╗ ██████╗  ██████╗ ███████╗██╗██╗     ███████╗
   * ██╔══██╗██╔══██╗██╔═══██╗██╔════╝██║██║     ██╔════╝
   * ██████╔╝██████╔╝██║   ██║█████╗  ██║██║     █████╗
   * ██╔═══╝ ██╔══██╗██║   ██║██╔══╝  ██║██║     ██╔══╝
   * ██║     ██║  ██║╚██████╔╝██║     ██║███████╗███████╗
   * ╚═╝     ╚═╝  ╚═╝ ╚═════╝ ╚═╝     ╚═╝╚══════╝╚══════╝
   *
   ***********************************************************************************/

// prof_init {{{
int pulp_rab_prof_init(void)
{
  // allocate buffer memory
  n_cyc_buf_response = (unsigned *)vmalloc(PROFILE_RAB_N_UPDATES * sizeof(unsigned));
  n_cyc_buf_update = (unsigned *)vmalloc(PROFILE_RAB_N_UPDATES * sizeof(unsigned));
  n_cyc_buf_setup = (unsigned *)vmalloc(PROFILE_RAB_N_REQUESTS * sizeof(unsigned));
  n_cyc_buf_cache_flush = (unsigned *)vmalloc(PROFILE_RAB_N_ELEMENTS * sizeof(unsigned));
  n_cyc_buf_get_user_pages = (unsigned *)vmalloc(PROFILE_RAB_N_ELEMENTS * sizeof(unsigned));
  if ((n_cyc_buf_response == NULL) || (n_cyc_buf_update == NULL) || (n_cyc_buf_setup == NULL) ||
      (n_cyc_buf_cache_flush == NULL) || (n_cyc_buf_get_user_pages == NULL)) {
    printk(KERN_WARNING "PULP - RAB: Could not allocate kernel memory for profiling buffers.\n");
    return -ENOMEM;
  }

  // initialize indices
  idx_buf_response = 0;
  idx_buf_update = 0;
  idx_buf_setup = 0;
  idx_buf_cache_flush = 0;
  idx_buf_get_user_pages = 0;

  // initialize accumulators
  n_cyc_tot_response = 0;
  n_cyc_tot_update = 0;
  n_cyc_tot_setup = 0;
  n_cyc_tot_cache_flush = 0;
  n_cyc_tot_get_user_pages = 0;

  #ifdef PROFILE_RAB_STR
  n_cyc_buf_cleanup = (unsigned *)vmalloc(PROFILE_RAB_N_REQUESTS * sizeof(unsigned));
  n_cyc_buf_map_sg = (unsigned *)vmalloc(PROFILE_RAB_N_ELEMENTS * sizeof(unsigned));
  if ((n_cyc_buf_cleanup == NULL) || (n_cyc_buf_map_sg == NULL)) {
    printk(KERN_WARNING "PULP - RAB: Could not allocate kernel memory for profiling buffers.\n");
    return -ENOMEM;
  }

  idx_buf_cleanup = 0;
  idx_buf_map_sg = 0;

  n_cyc_tot_cleanup = 0;
  n_cyc_tot_map_sg = 0;
  n_pages_setup = 0;
  n_cleanups = 0;
  n_slices_updated = 0;
  n_updates = 0;
  #endif

  #ifdef PROFILE_RAB_MH
  n_cyc_buf_schedule = (unsigned *)vmalloc(PROFILE_RAB_N_UPDATES * sizeof(unsigned));
  if (n_cyc_buf_schedule == NULL) {
    printk(KERN_WARNING "PULP - RAB: Could not allocate kernel memory for profiling buffers.\n");
    return -ENOMEM;
  }

  idx_buf_schedule = 0;

  n_cyc_tot_schedule = 0;
  n_first_misses = 0;
  n_misses = 0;
  #endif

  return 0;
}
// }}}

// prof_free {{{
void pulp_rab_prof_free(void)
{
  vfree(n_cyc_buf_response);
  vfree(n_cyc_buf_update);
  vfree(n_cyc_buf_setup);
  vfree(n_cyc_buf_cache_flush);
  vfree(n_cyc_buf_get_user_pages);

  #ifdef PROFILE_RAB_STR
  vfree(n_cyc_buf_cleanup);
  vfree(n_cyc_buf_map_sg);
  #endif

  #ifdef PROFILE_RAB_MH
  vfree(n_cyc_buf_schedule);
  #endif

  return;
}
// }}}

// prof_print {{{
void pulp_rab_prof_print(void)
{
  int i;

  // print buffers
  if (idx_buf_response) {
    printk(KERN_INFO "n_cyc_buf_response[i] = \n");
    for (i = 0; i < idx_buf_response; i++) {
      printk(KERN_INFO "%d \n", n_cyc_buf_response[i]);
    }
  }
  #ifdef PROFILE_RAB_MH
  if (idx_buf_schedule) {
    printk(KERN_INFO "n_cyc_buf_schedule[i] = \n");
    for (i = 0; i < idx_buf_schedule; i++) {
      printk(KERN_INFO "%d \n", n_cyc_buf_schedule[i]);
    }
  }
  #endif
  if (idx_buf_update) {
    printk(KERN_INFO "n_cyc_buf_update[i] = \n");
    for (i = 0; i < idx_buf_update; i++) {
      printk(KERN_INFO "%d \n", n_cyc_buf_update[i]);
    }
  }
  if (idx_buf_setup) {
    printk(KERN_INFO "n_cyc_buf_setup[i] = \n");
    for (i = 0; i < idx_buf_setup; i++) {
      printk(KERN_INFO "%d \n", n_cyc_buf_setup[i]);
    }
  }
  #ifdef PROFILE_RAB_STR
  if (idx_buf_cleanup) {
    printk(KERN_INFO "n_cyc_buf_cleanup[i] = \n");
    for (i = 0; i < idx_buf_cleanup; i++) {
      printk(KERN_INFO "%d \n", n_cyc_buf_cleanup[i]);
    }
  }
  #endif
  if (idx_buf_cache_flush) {
    printk(KERN_INFO "n_cyc_buf_cache_flush[i] = \n");
    for (i = 0; i < idx_buf_cache_flush; i++) {
      printk(KERN_INFO "%d \n", n_cyc_buf_cache_flush[i]);
    }
  }
  if (idx_buf_get_user_pages) {
    printk(KERN_INFO "n_cyc_buf_get_user_pages[i] = \n");
    for (i = 0; i < idx_buf_get_user_pages; i++) {
      printk(KERN_INFO "%d \n", n_cyc_buf_get_user_pages[i]);
    }
  }
  #ifdef PROFILE_RAB_STR
  if (idx_buf_map_sg) {
    printk(KERN_INFO "n_cyc_buf_map_sg[i] = \n");
    for (i = 0; i < idx_buf_map_sg; i++) {
      printk(KERN_INFO "%d \n", n_cyc_buf_map_sg[i]);
    }
  }
  #endif

  // update accumulators in shared memory
  iowrite32(n_cyc_tot_response, (void *)((unsigned long)(pulp->l3_mem) + N_CYC_TOT_RESPONSE_OFFSET_B));
  iowrite32(n_cyc_tot_update, (void *)((unsigned long)(pulp->l3_mem) + N_CYC_TOT_UPDATE_OFFSET_B));
  iowrite32(n_cyc_tot_setup, (void *)((unsigned long)(pulp->l3_mem) + N_CYC_TOT_SETUP_OFFSET_B));
  iowrite32(n_cyc_tot_cache_flush, (void *)((unsigned long)(pulp->l3_mem) + N_CYC_TOT_CACHE_FLUSH_OFFSET_B));
  iowrite32(n_cyc_tot_get_user_pages, (void *)((unsigned long)(pulp->l3_mem) + N_CYC_TOT_GET_USER_PAGES_OFFSET_B));

  // reset indices
  idx_buf_response = 0;
  idx_buf_update = 0;
  idx_buf_setup = 0;
  idx_buf_cache_flush = 0;
  idx_buf_get_user_pages = 0;

  // reset accumulators
  n_cyc_tot_response = 0;
  n_cyc_tot_update = 0;
  n_cyc_tot_setup = 0;
  n_cyc_tot_cache_flush = 0;
  n_cyc_tot_get_user_pages = 0;

  #ifdef PROFILE_RAB_STR
  iowrite32(n_cyc_tot_map_sg, (void *)((unsigned long)(pulp->l3_mem) + N_CYC_TOT_MAP_SG_OFFSET_B));
  iowrite32(n_cyc_tot_cleanup, (void *)((unsigned long)(pulp->l3_mem) + N_CYC_TOT_CLEANUP_OFFSET_B));
  iowrite32(n_pages_setup, (void *)((unsigned long)(pulp->l3_mem) + N_PAGES_SETUP_OFFSET_B));
  iowrite32(n_cleanups, (void *)((unsigned long)(pulp->l3_mem) + N_CLEANUPS_OFFSET_B));
  iowrite32(n_slices_updated, (void *)((unsigned long)(pulp->l3_mem) + N_SLICES_UPDATED_OFFSET_B));
  iowrite32(n_updates, (void *)((unsigned long)(pulp->l3_mem) + N_UPDATES_OFFSET_B));

  idx_buf_map_sg = 0;
  idx_buf_cleanup = 0;

  n_cyc_tot_map_sg = 0;
  n_cyc_tot_cleanup = 0;
  n_pages_setup = 0;
  n_cleanups = 0;
  n_slices_updated = 0;
  n_updates = 0;
  #endif

  #ifdef PROFILE_RAB_MH
  iowrite32(n_cyc_tot_schedule, (void *)((unsigned long)(pulp->l3_mem) + N_CYC_TOT_SCHEDULE_OFFSET_B));
  iowrite32(n_first_misses, (void *)((unsigned long)(pulp->l3_mem) + N_FIRST_MISSES_OFFSET_B));
  iowrite32(n_misses, (void *)((unsigned long)(pulp->l3_mem) + N_MISSES_OFFSET_B));

  idx_buf_schedule = 0;

  n_cyc_tot_schedule = 0;
  n_first_misses = 0;
  n_misses = 0;
  #endif

  return;
}
// }}}

#endif
// }}}
