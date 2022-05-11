/*
 * Compatibility layer between header-only library herodev.h and libsnitch
 *
 * Copyright 2022 ETH Zurich, University of Bologna
 *
 * Author: Noah Huetter <huettern@iis.ee.ethz.ch>
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

// Required and implemented symbols
// hero_dev_exe_start(pulp);
// hero_dev_exe_stop(pulp);
// hero_dev_exe_wait(pulp, HERO_DEV_DEFAULT_TIMEOUT);
// hero_dev_free_v_addr(pulp);
// hero_dev_get_clusters(pulp);
// hero_dev_get_l2_mem(pulp);
// hero_dev_get_l3_mem(pulp);
// hero_dev_get_nb_pe(pulp);
// hero_dev_init(pulp);
// hero_dev_l3_free(pulp, vir_ptr, phy_ptr);
// hero_dev_l3_malloc(pulp, size, (uintptr_t *)&phy_ptr);
// hero_dev_load_bin_from_mem(pulp, image_start, image->size);
// // hero_dev_mbox_read(pulp, nums, 2);
// // hero_dev_mbox_write(pulp, num_miss_handler_threads);
// // hero_dev_mmap(pulp) < 0)
// hero_dev_munmap(pulp);
// hero_dev_rab_free(pulp, 0x0);
// hero_dev_rab_soc_mh_disable(pulp);
// hero_dev_reserve_v_addr(pulp);
// hero_dev_reset(pulp, 0x1);

/// ------------------------------------

#include "debug.h"
#include "fesrv.h"
#include "herodev.h"
#include "libsnitch.h"
#include <pthread.h>
#include <stdint.h>

// ----------------------------------------------------------------------------
//
//   Macros
//
// ----------------------------------------------------------------------------
#define SHELL_RED "\033[0;31m"
#define SHELL_GRN "\033[0;32m"
#define SHELL_RST "\033[0m"

// ----------------------------------------------------------------------------
//
//   Global Data
//
// ----------------------------------------------------------------------------

struct gd {
  fesrv_t *fs;
  pthread_t fesrv_thd;
};
struct gd gd;

// ----------------------------------------------------------------------------
//
//   Static
//
// ----------------------------------------------------------------------------

/**
 * @brief Simple hex dump routine from https://gist.github.com/ccbrown/9722406
 *
 * @param data
 * @param size
 */
static void hexdump(const void *data, size_t size) {
  char ascii[17];
  size_t i, j;
  uint32_t pad = 4;

  if (LOG_TRACE > g_debuglevel)
    return;

  ascii[16] = '\0';
  for (i = 0; i < size; ++i) {
    if (i % 16 == 0)
      printf("%0*lx: ", pad, i);
    printf("%02X ", ((unsigned char *)data)[i]);
    if (((unsigned char *)data)[i] >= ' ' && ((unsigned char *)data)[i] <= '~') {
      ascii[i % 16] = ((unsigned char *)data)[i];
    } else {
      ascii[i % 16] = '.';
    }
    if ((i + 1) % 8 == 0 || i + 1 == size) {
      printf(" ");
      if ((i + 1) % 16 == 0) {
        printf("|  %s \n", ascii);
      } else if (i + 1 == size) {
        ascii[(i + 1) % 16] = '\0';
        if ((i + 1) % 16 <= 8) {
          printf(" ");
        }
        for (j = (i + 1) % 16; j < 16; ++j) {
          printf("   ");
        }
        printf("|  %s \n", ascii);
      }
    }
  }
}

/**
 * @brief Test memory access by writing and reading all elements
 * @details
 */
static int memtest(void *mem, size_t size, const char *cmt, uint8_t fillPat) {
  unsigned char rb;
  int err_cnt = 0;
  int test_cnt = 0;
  unsigned char *pmem = (unsigned char *)mem;

  pr_debug("[memtest] %s size %ldKiB\n", cmt, size / 1024);

  size_t byte_off;
  for (byte_off = 0; byte_off < size; byte_off++) {
    // if ((byte_off > 0) && ((byte_off % (64 * 1024)) == 0)) {
    //   pr_debug(".");
    //   fflush(stdout);
    // }

    pmem[byte_off] = byte_off % 0xff;
    rb = pmem[byte_off];
    if (rb != (byte_off % 0xff)) {
      pr_debug("[memtest] error at off 0x%08lx, write 0x%02lx, read %02x\n", byte_off,
               byte_off % 0xff, rb);
      err_cnt++;
    }
    test_cnt++;

    pmem[byte_off] = fillPat;
    rb = pmem[byte_off];
    if (rb != fillPat) {
      pr_debug("[memtest] error at off 0x%08lx, write 0x%02x, read %02x\n", byte_off, fillPat, rb);
      err_cnt++;
    }
    test_cnt++;
    if (err_cnt > 8) {
      pr_debug("aborting due to too many errors\n");
      break;
    }
  }
  pr_debug("\r[memtest] %s %s - size: %ld (%ldk), writes performed: %d, errors: %d (%.2f%%)\n",
           err_cnt ? SHELL_RED "FAIL" SHELL_RST : SHELL_GRN "PASS" SHELL_RST, cmt, size,
           size / 1024, test_cnt, err_cnt, 100.0 / test_cnt * err_cnt);
  return err_cnt;
}
// ----------------------------------------------------------------------------
//
//   RTL interface
//
// ----------------------------------------------------------------------------
uint32_t hero_dev_read32(const volatile uint32_t *base_addr, uint32_t off, char off_type) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
void hero_dev_write32(volatile uint32_t *base_addr, uint32_t off, char off_type, uint32_t value) {
  pr_error("%s unimplemented\n", __func__);
}
int hero_dev_mbox_read(const HeroDev *dev, uint32_t *buffer, size_t n_words) {
  return snitch_mbox_read((const snitch_dev_t *)dev->dev, buffer, n_words);
}
int hero_dev_mbox_write(HeroDev *dev, uint32_t word) {
  return snitch_mbox_write((snitch_dev_t *)dev->dev, word);
}
int hero_dev_reserve_v_addr(HeroDev *dev) {
  (void)dev;
  // Nothing to do here
  return 0;
}
int hero_dev_free_v_addr(const HeroDev *dev) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
void hero_dev_print_v_addr(HeroDev *dev) { pr_error("%s unimplemented\n", __func__); }
int hero_dev_mmap(HeroDev *dev) {
  int ret;

  // Stick to single-cluster for now
  dev->dev = malloc(sizeof(snitch_dev_t));
  snitch_dev_t *snitch = (snitch_dev_t *)dev->dev;
  ret = snitch_mmap(snitch, "/dev/snitch0");
  if (ret)
    return ret;

  // Assign L3 memory to RTL struct
  dev->l3_mem.v_addr = snitch->l3.v_addr;
  dev->l3_mem.p_addr = (size_t)snitch->l3.p_addr;
  dev->l3_mem.size = snitch->l3.size;

  return 0;
}
int hero_dev_munmap(HeroDev *dev) {
  snitch_dev_t *snitch = (snitch_dev_t *)dev->dev;

  // send exit code through mailbox
  snitch_mbox_write(snitch, MBOX_DEVICE_STOP);

  // wait a bit for the exit code
  time_t start;
  start = time(NULL);
  while(!gd.fs->coreExited) {
    if (difftime(time(NULL), start) >= 60.0 /* seconds */)
      break;
    usleep(10000);
  }
  if(!gd.fs->coreExited)
    pr_warn("No exit code received from cluster!\n");

  // kill fesvr
  gd.fs->abort = true;
  pthread_join(gd.fesrv_thd, NULL);

  // put to reset
  snitch_isolate(snitch, 1);

  // unmap
  // TODO: implement unmap

  return 0;
}
int hero_dev_clking_set_freq(HeroDev *dev, unsigned des_freq_mhz) {
  (void)dev;
  (void)des_freq_mhz;
  // libsnitch currently does not support vairable frequency
  return 0;
}
int hero_dev_clking_measure_freq(HeroDev *dev) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}

static void *fesrv_run_wrap(void *fs) {
  fesrv_run((fesrv_t *)fs);
  return NULL;
}

/** Initialize the memory mapped PULP device: disable reset and fetch enable, set up basic RAB
 *  mappings, enable mailbox interrupts, disable RAB miss interrupts, pass information to driver.

 *  NOTE: PULP needs to be mapped to memory before this function can be executed.

  \param    pulp pointer to the PulpDev structure

  \return   0 on success; negative value with an errno on errors.
 */
int hero_dev_init(HeroDev *dev) {
  int ret;
  snitch_dev_t *snitch = (snitch_dev_t *)dev->dev;

  // clear all interrupts
  snitch_ipi_clear(snitch, 0, ~0U);

  // setup front-end server. Do this here so that the host communication data is before any other
  // data in L3 to prevent overwriting thereof
  void *a2h_rb_addr;
  gd.fs = malloc(sizeof(fesrv_t));
  fesrv_init(gd.fs, snitch, &a2h_rb_addr);
  snitch->l3l->a2h_rb = (uint32_t)(uintptr_t)a2h_rb_addr;

  // start front end server
  gd.fs->abortAfter = 0;
  ret = pthread_create(&gd.fesrv_thd, NULL, fesrv_run_wrap, (void *)gd.fs);
  if (ret)
    return ret;

  // fill memory with pattern
  memtest(snitch->l1.v_addr, snitch->l1.size, "TCDM", 'T');

  return 0;
}


static void set_direct_tlb_map(snitch_dev_t *snitch, uint32_t idx, uint32_t low, uint32_t high) {
  struct axi_tlb_entry tlb_entry;
  tlb_entry.loc = AXI_TLB_NARROW;
  tlb_entry.flags = AXI_TLB_VALID;
  tlb_entry.idx = idx;
  tlb_entry.first = low;
  tlb_entry.last = high;
  tlb_entry.base = low;
  snitch_tlb_write(snitch, &tlb_entry);
  tlb_entry.loc = AXI_TLB_WIDE;
  snitch_tlb_write(snitch, &tlb_entry);
}

static void reset_tlbs(snitch_dev_t *snitch) {
  struct axi_tlb_entry tlb_entry;
  tlb_entry.flags = 0;
  tlb_entry.first = 0;
  tlb_entry.last = 0;
  tlb_entry.base = 0;
  for(unsigned idx = 0; idx < 32; ++idx) {
    tlb_entry.idx = idx;
    tlb_entry.loc = AXI_TLB_NARROW;
    snitch_tlb_write(snitch, &tlb_entry);
    tlb_entry.loc = AXI_TLB_WIDE;
    snitch_tlb_write(snitch, &tlb_entry);
  }
}

/** Reset device

  \param    dev  pointer to the HeroDev structure
  \param    full type of reset: 0 for Device reset, 1 for entire FPGA
 */
void hero_dev_reset(HeroDev *dev, unsigned full) {
  (void)full;
  snitch_dev_t *snitch = (snitch_dev_t *)dev->dev;

  // Add TLB entry for required ranges
  reset_tlbs(snitch);
  set_direct_tlb_map(snitch, 0, 0x01000000, 0x0101ffff); // BOOTROM
  set_direct_tlb_map(snitch, 1, 0x02000000, 0x02000fff); // SoC Control
  set_direct_tlb_map(snitch, 2, 0x04000000, 0x040fffff); // CLINT
  set_direct_tlb_map(snitch, 3, 0x10000000, 0x105fffff); // Quadrants
  set_direct_tlb_map(snitch, 4, 0x80000000, 0xffffffff); // HBM0/1

  (void)snitch_reset(snitch);
}
int hero_dev_get_nb_pe(HeroDev *dev) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
int hero_dev_boot(HeroDev *dev, const TaskDesc *task) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
int hero_dev_load_bin(HeroDev *dev, const char *name) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
int hero_dev_load_bin_from_mem(HeroDev *dev, void *ptr, unsigned size) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
/** Starts programm execution on PULP.

 \param    pulp pointer to the PulpDev structure
 */
void hero_dev_exe_start(HeroDev *dev) {
  snitch_dev_t *snitch = (snitch_dev_t *)dev->dev;
  unsigned cluster_idx = 0;
  struct BootData *bd;
  void *bd_phys;

  // Allocate space for bootdata
  bd = snitch_l3_malloc(snitch, sizeof(*bd), &bd_phys);

  // Populate bootdata
  bd->core_count = snitch->sci.compute_num + snitch->sci.dm_num;
  // hartid of first snitch core
  bd->hartid_base = 1;
  // Global cluster base address. Each cluster's TCDM is calculated using this offset,
  // tcdm_offset, hartid_base and mhartid CSR
  bd->tcdm_start = 0x10000000;
  // size of TCDM address space
  bd->tcdm_size = 0x20000;
  // offset between cluster address spaces
  bd->tcdm_offset = 0x40000;
  bd->global_mem_start = (uint32_t)(uintptr_t)(snitch->sci.l3_paddr + snitch->l3_data_offset);
  bd->global_mem_end = (uint32_t)(uintptr_t)(snitch->sci.l3_paddr + snitch->l3.size);
  // TODO: Handle multi-cluster
  bd->cluster_count = 1;
  // Let's pretend all clusters were in the same quadrant
  bd->s1_quadrant_count = 1;
  bd->clint_base = snitch->sci.clint_base;
  // unused
  bd->boot_addr = (uint32_t)(uintptr_t)snitch->sci.l3_paddr;

  // Set entry-point, bootrom pointer and l3 layout struct pointer
  snitch_scratch_reg_write(snitch, 0, (uint32_t)(uint64_t)snitch->l3.p_addr);
  snitch_scratch_reg_write(snitch, 1, (uint32_t)(uint64_t)bd_phys);
  snitch_scratch_reg_write(snitch, 2, (uint32_t)(uint64_t)snitch->l3l_p);

  pr_trace("Data in L1:\n");
  hexdump(snitch->l1.v_addr, 0x30);

  // Set log level from env
  snitch_set_device_loglevel(snitch, -1);

  // For single-cluster, set interrupt on first core of this cluster. It will bring up the rest of
  // the clusters through hierarchical wakeup
  pr_trace("Set interrupt on core %d\n", 1 + cluster_idx * 9);
  snitch_ipi_set(snitch, 0, 1 << (1 + cluster_idx * 9));

  sleep(1);
  pr_trace("Data in L1:\n");
  hexdump(snitch->l1.v_addr, 0x30);
}
/** Stops programm execution on PULP.

 \param    pulp pointer to the PulpDev structure
 */
void hero_dev_exe_stop(HeroDev *dev) { pr_error("%s unimplemented\n", __func__); }
int hero_dev_exe_wait(const HeroDev *dev, int timeout_s) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
int hero_dev_rab_req(const HeroDev *dev, unsigned addr_start, unsigned size_b, unsigned char prot,
                     unsigned char port, unsigned char date_exp, unsigned char date_cur,
                     unsigned char use_acp, unsigned char rab_lvl) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
void hero_dev_rab_free(const HeroDev *dev, unsigned char date_cur) {
  // not used for HERO_MEMCPY
  // pr_error("%s unimplemented\n", __func__);
  return;
}
int hero_dev_rab_req_striped(const HeroDev *dev, const TaskDesc *task, ElemPassType **pass_type,
                             int n_elements) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
void hero_dev_rab_free_striped(const HeroDev *dev) { pr_error("%s unimplemented\n", __func__); }
int hero_dev_rab_soc_mh_enable(const HeroDev *dev, const unsigned static_2nd_lvl_slices) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
int hero_dev_rab_soc_mh_disable(const HeroDev *dev) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
int hero_dev_rab_mh_enable(const HeroDev *dev, unsigned char use_acp, unsigned char rab_mh_lvl) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
int hero_dev_rab_mh_disable(const HeroDev *dev) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
int hero_dev_smmu_enable(const HeroDev *dev, const unsigned char flags) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
int hero_dev_smmu_disable(const HeroDev *dev) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
int hero_dev_rab_ax_log_read(const HeroDev *dev) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
int hero_dev_profile_info(const HeroDev *dev, ProfileInfo *profile_info) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
int hero_dev_offload_out(HeroDev *dev, TaskDesc *task) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
int hero_dev_offload_in(HeroDev *dev, TaskDesc *task) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
int hero_dev_offload_get_pass_type(const TaskDesc *task, ElemPassType **pass_type) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
int hero_dev_offload_rab_setup(const HeroDev *dev, const TaskDesc *task, ElemPassType **pass_type,
                               int n_ref) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
int hero_dev_offload_rab_free(const HeroDev *dev, const TaskDesc *task,
                              const ElemPassType **pass_type, int n_ref) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
int hero_dev_offload_pass_desc(HeroDev *dev, const TaskDesc *task, const ElemPassType **pass_type) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
int hero_dev_offload_get_desc(const HeroDev *dev, TaskDesc *task, const ElemPassType **pass_type) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
int hero_dev_offload_l3_copy_raw_out(HeroDev *dev, TaskDesc *task, const ElemPassType **pass_type) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}

int hero_dev_offload_l3_copy_raw_in(HeroDev *dev, const TaskDesc *task,
                                    const ElemPassType **pass_type) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
/** Allocate a chunk of memory in contiguous L3.

  \param    pulp   pointer to the PulpDev structure
  \param    size_b size in Bytes of the requested chunk
  \param    p_addr pointer to store the physical address to

  \return   virtual user-space address for host
 */
uintptr_t hero_dev_l3_malloc(HeroDev *dev, unsigned size_b, uintptr_t *p_addr) {
  return (uintptr_t)snitch_l3_malloc((snitch_dev_t *)dev->dev, size_b, (void *)p_addr);
}
/** Free memory previously allocated in contiguous L3.

 \param    dev   pointer to the snitch_dev_t structure
 \param    v_addr pointer to unsigned containing the virtual address
 \param    p_addr pointer to unsigned containing the physical address

 */
void hero_dev_l3_free(HeroDev *dev, uintptr_t v_addr, uintptr_t p_addr) {
  snitch_l3_free((snitch_dev_t *)dev->dev, (void *)v_addr, (void *)p_addr);
}
int hero_dev_dma_xfer(const HeroDev *dev, uintptr_t addr_l3, uintptr_t addr_pulp, size_t size_b,
                      int host_read) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
int hero_dev_omp_offload_task(HeroDev *dev, TaskDesc *task) {
  pr_error("%s unimplemented\n", __func__);
  return 0;
}
