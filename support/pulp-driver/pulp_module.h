/*
 * This file is part of the PULP device driver.
 *
 * Copyright (C) 2018 ETH Zurich, University of Bologna
 *
 * Author: Pirmin Vogel <vogelpi@iis.ee.ethz.ch>
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
#ifndef _PULP_MODULE_H_
#define _PULP_MODULE_H_

#include <linux/cdev.h> /* cdev struct */
#include <linux/device.h> /* device struct */

/*
 * Debug flags
 */
#ifndef DEBUG_LEVEL
  #define DEBUG_LEVEL 0
#endif

#ifndef DEBUG_LEVEL_PULP
  #define DEBUG_LEVEL_PULP DEBUG_LEVEL
#endif
#ifndef DEBUG_LEVEL_CTRL
  #define DEBUG_LEVEL_CTRL DEBUG_LEVEL
#endif
#ifndef DEBUG_LEVEL_OF
  #define DEBUG_LEVEL_OF DEBUG_LEVEL
#endif
#ifndef DEBUG_LEVEL_MEM
  #define DEBUG_LEVEL_MEM DEBUG_LEVEL
#endif
#ifndef DEBUG_LEVEL_RAB
  #define DEBUG_LEVEL_RAB DEBUG_LEVEL
#endif
#ifndef DEBUG_LEVEL_RAB_STR
  #define DEBUG_LEVEL_RAB_STR DEBUG_LEVEL
#endif
#ifndef DEBUG_LEVEL_RAB_MH
  #define DEBUG_LEVEL_RAB_MH DEBUG_LEVEL
#endif
#ifndef DEBUG_LEVEL_RAB_SMMU
  #define DEBUG_LEVEL_SMMU DEBUG_LEVEL
#endif
#ifndef DEBUG_LEVEL_SMMU_FH
  #define DEBUG_LEVEL_SMMU_FH DEBUG_LEVEL
#endif
#ifndef DEBUG_LEVEL_DMA
  #define DEBUG_LEVEL_DMA DEBUG_LEVEL
#endif
#ifndef DEBUG_LEVEL_MBOX
  #define DEBUG_LEVEL_MBOX DEBUG_LEVEL
#endif

/*
 * Defines
 */
// Shared defines between kernel and user-space
#include "pulp_common.h"

//#define PROFILE_DMA
//#define PROFILE_RAB_MH_SIMPLE
#if PLATFORM == ZEDBOARD || PLATFORM == ZC706 || PLATFORM == MINI_ITX
  //#define PROFILE_RAB_STR
  //#define PROFILE_RAB_MH
#endif

#if PLATFORM == JUNO
  #include "juno.h"
#elif PLATFORM == TE0808
  #include "zynqmp.h"
#else // PLATFORM == ZEDBOARD || PLATFORM == ZC706 || PLATFORM == MINI_ITX
  #include "zynq.h"
#endif

/*
 * Constants for profiling
 */
#if defined(PROFILE_RAB_STR) || defined(PROFILE_RAB_MH)
  #define N_CYC_TOT_RESPONSE_OFFSET_B 0x00
  #define N_CYC_TOT_UPDATE_OFFSET_B 0x04
  #define N_CYC_TOT_SETUP_OFFSET_B 0x08
  #define N_CYC_TOT_CLEANUP_OFFSET_B 0x0c
  #define N_UPDATES_OFFSET_B 0x10
  #define N_SLICES_UPDATED_OFFSET_B 0x14
  #define N_PAGES_SETUP_OFFSET_B 0x18
  #define N_CLEANUPS_OFFSET_B 0x1c

  #define N_CYC_TOT_CACHE_FLUSH_OFFSET_B 0x20
  #define N_CYC_TOT_GET_USER_PAGES_OFFSET_B 0x24
  #define N_CYC_TOT_MAP_SG_OFFSET_B 0x28

  #define N_MISSES_OFFSET_B 0x2C
  #define N_FIRST_MISSES_OFFSET_B 0x30
  #define N_CYC_TOT_SCHEDULE_OFFSET_B 0x34

  #define PROFILE_RAB_N_UPDATES 100000
  #define PROFILE_RAB_N_REQUESTS 100
  #define PROFILE_RAB_N_ELEMENTS (PROFILE_RAB_N_REQUESTS * 10)
#endif

/*
 * Macros
 */
#if PLATFORM == JUNO || PLATFORM == TE0808
  #define IOWRITE_L(value, addr) (iowrite64(value, addr))
  #define IOREAD_L(addr) (ioread64(addr))
#else
  #define IOWRITE_L(value, addr) (iowrite32(value, addr))
  #define IOREAD_L(addr) (ioread32(addr))
#endif

/*
 * Type Definitions
 */
typedef struct {
  dev_t dev; // device number
  struct file_operations *fops;
  struct cdev cdev;
  int minor;
  int major;
  // device tree
  struct device *dt_dev_ptr;
  // interrupts
  int intr_reg_irq;
  int irq_mbox;
  int irq_rab_host_miss;
  int irq_rab_host_multi;
  int irq_rab_host_prot;
  int irq_rab_pulp_miss;
  int irq_rab_pulp_multi;
  int irq_rab_pulp_prot;
  int irq_eoc;
  int irq_rab_mhr_full;
  // virtual address pointers for ioremap_nocache()
  void *mbox;
  void *rab_config;
  void *gpio;
#ifdef GPIO_EXT_RESET_ADDR
  void *gpio_reset;
#endif
  void *soc_periph;
  void *clusters;
  void *l3_mem;
  void *l2_mem;
#if INTR_REG_BASE_ADDR
  void *intr_reg;
#endif
#if CLKING_BASE_ADDR
  void *clking;
#endif
#if PLATFORM == TE0808
  void *cci;
  void *smmu;
#endif // PLATFORM
#if PLATFORM == ZEDBOARD || PLATFORM == ZC706 || PLATFORM == MINI_ITX
  void *slcr;
#endif // PLATFORM
#if PLATFORM == ZEDBOARD || PLATFORM == ZC706 || PLATFORM == MINI_ITX || PLATFORM == TE0808
  void *uart;
#endif // PLATFORM
#if RAB_AX_LOG_EN == 1
  void *rab_ar_log;
  void *rab_aw_log;
  void *rab_cfg_log;
#endif // RAB_AX_LOG_EN == 1
} PulpDev;

#endif // _PULP_MODULE_H_
