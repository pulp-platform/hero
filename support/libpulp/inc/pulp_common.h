/*
 * This file is part of the PULP user-space and kernel-space libraries.
 *
 * Copyright 2018 ETH Zurich, University of Bologna
 *
 * Author: Pirmin Vogel <vogelpi@iis.ee.ethz.ch>
 *         Koen Wolters <kwolters@student.ethz.ch>
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

#ifndef PULP_COMMON_H
#define PULP_COMMON_H

#define ZEDBOARD 1
#define ZC706 2
#define MINI_ITX 3
#define JUNO 4
#define TE0808 5
#define ARIANE 6
#define ZYNQMP 7

#ifndef PLATFORM
  #error "Define PLATFORM!"
#endif

/*
 * Accelerator architecture
 */
#define CHIP_BIGPULP 7
#define CHIP_BIGPULP_Z_7020 8
#define CHIP_BIGPULP_Z_7045 9
#define CHIP_HERO_URANIA 38

#define PULP_CHIP_FAMILY_STR bigpulp

#define PULP_CHIP_FAMILY CHIP_BIGPULP
#if PLATFORM == ZEDBOARD
  #define PULP_CHIP CHIP_BIGPULP_Z_7045
#elif PLATFORM == ZC706 || PLATFORM == MINI_ITX || PLATFORM == TE0808 || PLATFORM == ZYNQMP
  #define PULP_CHIP CHIP_BIGPULP_Z_7045
#elif PLATFORM == ARIANE
  #define PULP_CHIP CHIP_HERO_URANIA
#else // PLATFORM == JUNO
  #define PULP_CHIP CHIP_BIGPULP
#endif

/*
 * Host memory map - Part 1 -- see Vivado block diagram
 */
#define MAX_CLUSTERS 16

#if PLATFORM == ZEDBOARD || PLATFORM == ZC706 || PLATFORM == MINI_ITX

  #define H_GPIO_BASE_ADDR 0x51000000
  #define CLKING_BASE_ADDR 0x51010000
  #define RAB_CONFIG_BASE_ADDR 0x51030000
  #define INTR_REG_BASE_ADDR 0x51050000

  #if PLATFORM == ZEDBOARD

    #define RAB_AX_LOG_EN 0
    #define L3_MEM_SIZE_MB 16

  #elif PLATFORM == ZC706 || PLATFORM == MINI_ITX

    #define RAB_AR_LOG_BASE_ADDR 0x51100000
    #define RAB_AW_LOG_BASE_ADDR 0x51200000
    // #define RAB_CFG_LOG_BASE_ADDR TODO (also in HW)

    #define RAB_AX_LOG_EN 1
    #define RAB_AX_LOG_SIZE_B 0x6000 // size of BRAM, 192 KiB = 2 Ki entries
    #define RAB_AX_LOG_BUF_SIZE_B 0x600000 // size of buffer in driver, 6 MiB = 512 Ki entries
    #define RAB_CFG_LOG_SIZE_B 0x30000 // size of BRAM, 196 KiB = 16 Ki entries

    #define L3_MEM_SIZE_MB 128

  #endif // PLATFORM

#elif PLATFORM == JUNO

  #define H_GPIO_BASE_ADDR 0x6E000000
  #define CLKING_BASE_ADDR 0x6E010000
  #define RAB_CONFIG_BASE_ADDR 0x6E030000
  #define INTR_REG_BASE_ADDR 0x6E050000
  #define RAB_AR_LOG_BASE_ADDR 0x6E100000
  #define RAB_AW_LOG_BASE_ADDR 0x6E200000
  #define RAB_CFG_LOG_BASE_ADDR 0x6E300000

  #define RAB_AX_LOG_EN 1
  #define RAB_AX_LOG_SIZE_B 0xC0000 // size of BRAM, 786 KiB = 64 Ki entries
  #define RAB_CFG_LOG_SIZE_B 0x30000 // size of BRAM, 196 KiB = 16 Ki entries
  #define RAB_AX_LOG_BUF_SIZE_B 0x6000000 // size of buffer in driver, 96 MiB = 8 Mi entries

  #define L3_MEM_SIZE_MB 128

#elif PLATFORM == ARIANE

  #define H_GPIO_BASE_ADDR 0x40000000
  #define CLKING_BASE_ADDR 0x00000000 // not supported
  #define RAB_CONFIG_BASE_ADDR 0x60030000
  #define INTR_REG_BASE_ADDR 0x00000000 // not supported

  #define RAB_AX_LOG_EN 0

  #define L3_MEM_SIZE_MB 128

#elif PLATFORM == TE0808

  #define H_GPIO_BASE_ADDR 0xAE000000
  #define CLKING_BASE_ADDR 0xAE010000
  #define RAB_CONFIG_BASE_ADDR 0xAE030000
  #define INTR_REG_BASE_ADDR 0xAE050000
  #define RAB_AR_LOG_BASE_ADDR 0xAE100000
  #define RAB_AW_LOG_BASE_ADDR 0xAE200000
  #define RAB_CFG_LOG_BASE_ADDR 0xAE300000

  #define RAB_AX_LOG_EN 1
  #define RAB_AX_LOG_SIZE_B 0xC0000 // size of BRAM, 786 KiB = 64 Ki entries
  #define RAB_CFG_LOG_SIZE_B 0x30000 // size of BRAM, 196 KiB = 16 Ki entries
  #define RAB_AX_LOG_BUF_SIZE_B 0x6000000 // size of buffer in driver, 96 MiB = 8 Mi entries

  #define L3_MEM_SIZE_MB 128

#else // PLATFORM == ZYNQMP

  #define H_GPIO_BASE_ADDR 0xA9000000
  #define CLKING_BASE_ADDR 0x00000000 // not supported
  #define RAB_CONFIG_BASE_ADDR 0xA8000000
  #define INTR_REG_BASE_ADDR 0xA9100000

  #define RAB_AX_LOG_EN 0

  #define L3_MEM_SIZE_MB 128

#endif // PLATFORM

#define H_GPIO_SIZE_B 0x1000
#define CLKING_SIZE_B 0x1000
#define INTR_REG_SIZE_B 0x1000
#define RAB_CONFIG_SIZE_B 0x10000

/*
 * Host memory map - Part 2 - PULP -- see Vivado block diagram
 */
#if PLATFORM == ZEDBOARD || PLATFORM == ZC706 || PLATFORM == MINI_ITX
  #define PULP_H_BASE_ADDR 0x40000000 // Address at which the host sees PULP
  #define L1_MEM_H_BASE_ADDR PULP_H_BASE_ADDR
  #define L2_MEM_H_BASE_ADDR 0x4C000000
  #define L3_MEM_H_BASE_ADDR (DRAM_SIZE_MB - L3_MEM_SIZE_MB) * 1024 * 1024 // = 0x38000000 for 1024 MB DRAM and 128 MB L3
  #define MBOX_H_BASE_ADDR 0x4A120000 // Interface 0
  #define SOC_PERIPHERALS_H_BASE_ADDR 0x4A100000
#elif PLATFORM == JUNO
  #define PULP_H_BASE_ADDR 0x60000000 // Address at which the host sees PULP
  #define L1_MEM_H_BASE_ADDR PULP_H_BASE_ADDR
  #define L2_MEM_H_BASE_ADDR 0x67000000
  #define L3_MEM_H_BASE_ADDR (0xA00000000LL - L3_MEM_SIZE_B)
  #define MBOX_H_BASE_ADDR 0x65120000 // Interface 0
  #define SOC_PERIPHERALS_H_BASE_ADDR 0x65100000
#elif PLATFORM == ARIANE
  #define PULP_H_BASE_ADDR 0x50000000
  #define L1_MEM_H_BASE_ADDR PULP_H_BASE_ADDR
  #define L2_MEM_H_BASE_ADDR 0x5C000000
  #define L3_MEM_H_BASE_ADDR (0xC0000000 - L3_MEM_SIZE_B)
  #define MBOX_H_BASE_ADDR 0x5A120000
  #define SOC_PERIPHERALS_H_BASE_ADDR 0x5A100000
#elif PLATFORM == TE0808
  #define PULP_H_BASE_ADDR 0xA0000000 // Address at which the host sees PULP
  #define L1_MEM_H_BASE_ADDR PULP_H_BASE_ADDR
  #define L2_MEM_H_BASE_ADDR 0xA7000000
  #define L3_MEM_H_BASE_ADDR (0x80000000 - L3_MEM_SIZE_B)
  #define MBOX_H_BASE_ADDR 0xA5120000 // Interface 0
  #define SOC_PERIPHERALS_H_BASE_ADDR 0xA5100000
#else // PLATFORM == ZYNQMP
  #define PULP_H_BASE_ADDR 0xA0000000 // Address at which the host sees PULP
  #define L1_MEM_H_BASE_ADDR PULP_H_BASE_ADDR
  #define L2_MEM_H_BASE_ADDR 0xA7000000
  #define L3_MEM_H_BASE_ADDR (0x80000000 - L3_MEM_SIZE_B)
  #define MBOX_H_BASE_ADDR   0xA6000000 // FIXME
  #define SOC_PERIPHERALS_H_BASE_ADDR 0xA5100000
#endif // PLATFORM

/*
 * PULP memory map -- see PULP SDK and PULP HW
 */
#define PULP_BASE_ADDR 0x10000000
#define MBOX_BASE_ADDR 0x1c00f100
#define L2_MEM_BASE_ADDR 0x1C000000
#define L3_MEM_BASE_ADDR 0x80000000 // address of the contiguous L3
#define PGD_BASE_ADDR 0x20000000 // address of the top-level page table of user-space process

#define CLUSTER_PERIPHERALS_OFFSET_B 0x200000
#define TIMER_OFFSET_B 0x400

#define TIMER_CLUSTER_OFFSET_B (CLUSTER_PERIPHERALS_OFFSET_B + TIMER_OFFSET_B)
#define TIMER_START_OFFSET_B (TIMER_CLUSTER_OFFSET_B + 0x00)
#define TIMER_STOP_OFFSET_B (TIMER_CLUSTER_OFFSET_B + 0x04)
#define TIMER_RESET_OFFSET_B (TIMER_CLUSTER_OFFSET_B + 0x08)
#define TIMER_GET_TIME_LO_OFFSET_B (TIMER_CLUSTER_OFFSET_B + 0x0c)
#define TIMER_GET_TIME_HI_OFFSET_B (TIMER_CLUSTER_OFFSET_B + 0x10)

#define BBMUX_CLKGATE_OFFSET_B 0x800
#define EU_SW_EVENTS_OFFSET_B 0x600

/**
 * PULP config -- see PULP SDK and PULP HW
 */
#if PLATFORM == ZEDBOARD
  #define N_CLUSTERS 1
  #define N_CORES 2
  #define L2_MEM_SIZE_KB 64
  #define L1_MEM_SIZE_KB 32
  #define PULP_DEFAULT_FREQ_MHZ 25
  #define CLKING_INPUT_FREQ_MHZ 50
  #define RAB_L1_N_SLICES_PORT_1 8
#elif PLATFORM == MINI_ITX || PLATFORM == ZC706
  #define N_CLUSTERS 1
  #define N_CORES 8
  #define L2_MEM_SIZE_KB 256
  #define L1_MEM_SIZE_KB 256
  #define PULP_DEFAULT_FREQ_MHZ 50
  #define CLKING_INPUT_FREQ_MHZ 100
#elif PLATFORM == TE0808
  #define N_CLUSTERS 1
  #define N_CORES 8
  #define L2_MEM_SIZE_KB 256
  #define L1_MEM_SIZE_KB 256
  #define PULP_DEFAULT_FREQ_MHZ 50
  #define CLKING_INPUT_FREQ_MHZ 100
#elif PLATFORM == ARIANE
  #define N_CLUSTERS 1
  #define N_CORES 2
  #define L2_MEM_SIZE_KB 256
  #define L1_MEM_SIZE_KB 256
  #define PULP_DEFAULT_FREQ_MHZ 50
  #define CLKING_INPUT_FREQ_MHZ 100
#elif PLATFORM == JUNO
  #define N_CLUSTERS 4
  #define N_CORES 8
  #define L2_MEM_SIZE_KB 256
  #define L1_MEM_SIZE_KB 256
  #define PULP_DEFAULT_FREQ_MHZ 25
  #define CLKING_INPUT_FREQ_MHZ 100
#else // PLATFORM == ZYNQMP
  #define N_CLUSTERS 1
  #define N_CORES 8
  #define L2_MEM_SIZE_KB 128
  #define L1_MEM_SIZE_KB 128
  #define PULP_DEFAULT_FREQ_MHZ 50
  #define CLKING_INPUT_FREQ_MHZ 50
#endif

#if N_CLUSTERS > MAX_CLUSTERS
  #error "Too many computation clusters"
#endif

#define CLUSTER_SIZE_MB 4

#define L1_MEM_SIZE_B (L1_MEM_SIZE_KB * 1024)
#define L2_MEM_SIZE_B (L2_MEM_SIZE_KB * 1024)
#define L3_MEM_SIZE_B (L3_MEM_SIZE_MB * 1024 * 1024)

#define CLUSTER_SIZE_B (CLUSTER_SIZE_MB * 1024 * 1024)
#define CLUSTERS_SIZE_B (N_CLUSTERS * CLUSTER_SIZE_B)

#define PULP_SIZE_B 0x10000000
#define SOC_PERIPHERALS_SIZE_B 0x50000
#define MBOX_SIZE_B 0x1000 // Interface 0 only

/*
 * General settings
 */
#define PULP_N_DEV_NUMBERS 1
#define CLUSTER_MASK (unsigned)((1 << N_CLUSTERS) - 1)

/*
 * Interrupts -- see bigpulp*_top.sv
 */

#if PLATFORM == ZYNQMP
#define INTR_EOC_0 7
#define INTR_EOC_N 7 + (N_CLUSTERS - 1) // max 15

#define INTR_MBOX 16
#define INTR_RAB_MISS 17
#define INTR_RAB_MULTI 18
#define INTR_RAB_PROT 19
#define INTR_RAB_MHR_FULL 20
#define INTR_RAB_AR_LOG_FULL 21
#define INTR_RAB_AW_LOG_FULL 22
#define INTR_RAB_CFG_LOG_FULL 23
#else
#define INTR_EOC_0 0
#define INTR_EOC_N (N_CLUSTERS - 1) // max 15

#define INTR_MBOX 16
#define INTR_RAB_MISS 17
#define INTR_RAB_MULTI 18
#define INTR_RAB_PROT 19
#define INTR_RAB_MHR_FULL 20
#define INTR_RAB_AR_LOG_FULL 21
#define INTR_RAB_AW_LOG_FULL 22
#define INTR_RAB_CFG_LOG_FULL 23
#endif

/*
 * PULP GPIOs -- see bigpulp*_top.sv
 */
#define GPIO_CLUSTER_OFFSET 0
#define GPIO_EOC_0 0
#define GPIO_EOC_N (N_CLUSTERS - 1) // max 15

#if PLATFORM == ARIANE
  #define GPIO_HOST2PULP_OFFSET 0
  #define GPIO_PULP2HOST_OFFSET -1

  #define GPIO_INTR_RAB_MISS_DIS 2 // NOTE: not used
  #define GPIO_RAB_AX_LOG_EN 3 // NOTE: not used

  #define GPIO_RST_N 1
  #define GPIO_CLK_EN -1
#elif PLATFORM == ZYNQMP
  #define GPIO_HOST2PULP_OFFSET 0
  #define GPIO_PULP2HOST_OFFSET -1

  #define GPIO_INTR_RAB_MISS_DIS 2 // NOTE: not used
  #define GPIO_RAB_AX_LOG_EN 3 // NOTE: not used

  #define GPIO_EXT_RESET_ADDR 0xFF0A0054
  #define GPIO_EXT_RESET_SIZE_B 8

  #define GPIO_RST_N 31
  #define GPIO_CLK_EN -1
#else
  #define GPIO_HOST2PULP_OFFSET 8
  #define GPIO_PULP2HOST_OFFSET 0

  #define GPIO_INTR_RAB_MISS_DIS 17

  #define GPIO_RST_N 31
  #define GPIO_CLK_EN 30
  #define GPIO_RAB_CFG_LOG_RDY 27
  #define GPIO_RAB_AR_LOG_RDY 28
  #define GPIO_RAB_AW_LOG_RDY 29
  #define GPIO_RAB_AR_LOG_CLR 28
  #define GPIO_RAB_AW_LOG_CLR 29
  #define GPIO_RAB_AX_LOG_EN 27
  #define GPIO_RAB_CFG_LOG_CLR 26
#endif

/*
 * Mailbox
 */
#define MBOX_FIFO_DEPTH 16
#define MBOX_WRDATA_OFFSET_B 0x0
#define MBOX_RDDATA_OFFSET_B 0x10
#define MBOX_STATUS_OFFSET_B 0x20
#define MBOX_ERROR_OFFSET_B 0x30
#define MBOX_IS_OFFSET_B 0x60
#define MBOX_IE_OFFSET_B 0x70

/*
 * RAB
 */
#define RAB_CONFIG_MAX_GAP_SIZE_B 0x1000 // one page

#define RAB_FLAGS_DRV_CONST 0b00000001 // const mapping
#define RAB_FLAGS_DRV_STRIPED 0b00000010 // striped mapping
#define RAB_FLAGS_DRV_EVERY 0b00000100 // set up in every RAB mapping
#define RAB_FLAGS_DRV_FIXED 0b00001000 // mapping fixed for the driver

#define RAB_FLAGS_HW_EN 0b00000001 // enable mapping
#define RAB_FLAGS_HW_READ 0b00000010 // enable read
#define RAB_FLAGS_HW_WRITE 0b00000100 // enable write
#define RAB_FLAGS_HW_CC 0b00001000 // cache-coherent mapping

#define RAB_SLICE_SIZE_B 0x20
#define RAB_SLICE_BASE_OFFSET_B 0x20
#define RAB_SLICE_ADDR_START_OFFSET_B 0x0
#define RAB_SLICE_ADDR_END_OFFSET_B 0x8
#define RAB_SLICE_ADDR_OFFSET_OFFSET_B 0x10
#define RAB_SLICE_FLAGS_OFFSET_B 0x18

#define RAB_MH_ADDR_FIFO_OFFSET_B 0x0
#define RAB_MH_META_FIFO_OFFSET_B 0x8

#define RAB_WAKEUP_OFFSET_B 0x0

#define RAB_AX_LOG_PRINT_FORMAT 0 // 0 = DEBUG, 1 = MATLAB

#define RAB_CONFIG_N_BITS_PORT 1
#define RAB_CONFIG_N_BITS_ACP 1
#define RAB_CONFIG_N_BITS_LVL 2
#define RAB_CONFIG_N_BITS_PROT 3
#define RAB_CONFIG_N_BITS_DATE 8

#define RAB_MAX_DATE BIT_MASK_GEN(RAB_CONFIG_N_BITS_DATE)
#define RAB_MAX_DATE_MH (RAB_MAX_DATE - 2)

/*
 * System-Level Control Register
 */
#if PLATFORM == ZEDBOARD || PLATFORM == ZC706 || PLATFORM == MINI_ITX
  #define SLCR_SIZE_B 0x1000
  #define SLCR_FPGA_RST_CTRL_OFFSET_B 0x240
  #define SLCR_FPGA_OUT_RST 1
  #define SLCR_FPGA0_THR_CNT_OFFSET_B 0x178
  #define SLCR_FPGA0_THR_STA_OFFSET_B 0x17C
#endif

/*
 * Performance Monitor Unit
 */
#if PLATFORM == ZEDBOARD || PLATFORM == ZC706 || PLATFORM == MINI_ITX
  #define ARM_PMU_CLK_DIV 64 // clock divider for clock cycle counter
#endif

/*
 * Clocking
 */
#define CLKING_CONFIG_REG_0_OFFSET_B 0x200
#define CLKING_CONFIG_REG_2_OFFSET_B 0x208
#define CLKING_CONFIG_REG_5_OFFSET_B 0x214
#define CLKING_CONFIG_REG_8_OFFSET_B 0x220
#define CLKING_CONFIG_REG_23_OFFSET_B 0x25C
#define CLKING_STATUS_REG_OFFSET_B 0x4

#if PLATFORM == ZEDBOARD || PLATFORM == MINI_ITX || PLATFORM == ZC706
  #define ARM_CLK_FREQ_MHZ 666
#elif PLATFORM == TE0808
  #define ARM_CLK_FREQ_MHZ 1200
#else // JUNO
  #define ARM_CLK_FREQ_MHZ 1100 // A57 overdrive
#endif

/*
 * Macros
 */
// General
#define BIT_N_SET(n) (1UL << (n))
#define BIT_GET(y, mask) (y & mask)
#define BIT_SET(y, mask) (y |= (mask))
#define BIT_CLEAR(y, mask) (y &= ~(mask))
#define BIT_FLIP(y, mask) (y ^= (mask))
// Create a bitmask of length len.
#define BIT_MASK_GEN(len) (BIT_N_SET(len) - 1)
// Create a bitfield mask of length len starting at bit start.
#define BF_MASK_GEN(start, len) (BIT_MASK_GEN(len) << (start))
// Prepare a bitmask for insertion or combining.
#define BF_PREP(x, start, len) (((x)&BIT_MASK_GEN(len)) << (start))
// Extract a bitfield of length len starting at bit start from y.
#define BF_GET(y, start, len) (((y) >> (start)) & BIT_MASK_GEN(len))
// Insert a new bitfield value x into y.
#define BF_SET(y, x, start, len) (y = ((y) & ~BF_MASK_GEN(start, len)) | BF_PREP(x, start, len))

// RAB
#define RAB_GET_FLAGS_HW(flags_hw, request) (flags_hw = BF_GET(request, 0, RAB_CONFIG_N_BITS_PROT + RAB_CONFIG_N_BITS_ACP))
#define RAB_SET_FLAGS_HW(request, flags_hw) (BF_SET(request, flags_hw, 0, RAB_CONFIG_N_BITS_PROT + RAB_CONFIG_N_BITS_ACP))

#define RAB_GET_PROT(prot, request) (prot = request & 0x7)
#define RAB_SET_PROT(request, prot) (BF_SET(request, prot, 0, RAB_CONFIG_N_BITS_PROT))

#define RAB_GET_ACP(use_acp, request) (use_acp = BF_GET(request, RAB_CONFIG_N_BITS_PROT, RAB_CONFIG_N_BITS_ACP))
#define RAB_SET_ACP(request, use_acp) (BF_SET(request, use_acp, RAB_CONFIG_N_BITS_PROT, RAB_CONFIG_N_BITS_ACP))

#define RAB_GET_PORT(port, request) \
  (port = BF_GET(request, RAB_CONFIG_N_BITS_PROT + RAB_CONFIG_N_BITS_ACP, RAB_CONFIG_N_BITS_PORT))
#define RAB_SET_PORT(request, port) \
  (BF_SET(request, port, RAB_CONFIG_N_BITS_PROT + RAB_CONFIG_N_BITS_ACP, RAB_CONFIG_N_BITS_PORT))

#define RAB_GET_LVL(rab_lvl, request) \
  (rab_lvl = BF_GET(request, RAB_CONFIG_N_BITS_PROT + RAB_CONFIG_N_BITS_PORT + RAB_CONFIG_N_BITS_ACP, RAB_CONFIG_N_BITS_LVL))
#define RAB_SET_LVL(request, rab_lvl) \
  (BF_SET(request, rab_lvl, RAB_CONFIG_N_BITS_PROT + RAB_CONFIG_N_BITS_PORT + RAB_CONFIG_N_BITS_ACP, RAB_CONFIG_N_BITS_LVL))

#define RAB_GET_DATE_EXP(date_exp, request)                                                                           \
  (date_exp = BF_GET(request,                                                                                         \
                     RAB_CONFIG_N_BITS_PROT + RAB_CONFIG_N_BITS_PORT + RAB_CONFIG_N_BITS_ACP + RAB_CONFIG_N_BITS_LVL, \
                     RAB_CONFIG_N_BITS_DATE))
#define RAB_SET_DATE_EXP(request, date_exp)                                                                \
  (BF_SET(request, date_exp,                                                                               \
          RAB_CONFIG_N_BITS_PROT + RAB_CONFIG_N_BITS_PORT + RAB_CONFIG_N_BITS_ACP + RAB_CONFIG_N_BITS_LVL, \
          RAB_CONFIG_N_BITS_DATE))

#define RAB_GET_DATE_CUR(date_cur, request)                                                                             \
  (date_cur = BF_GET(request,                                                                                           \
                     RAB_CONFIG_N_BITS_PROT + RAB_CONFIG_N_BITS_PORT + RAB_CONFIG_N_BITS_DATE + RAB_CONFIG_N_BITS_ACP + \
                       RAB_CONFIG_N_BITS_LVL,                                                                           \
                     RAB_CONFIG_N_BITS_DATE))
#define RAB_SET_DATE_CUR(request, date_cur)                                                                  \
  (BF_SET(request, date_cur,                                                                                 \
          RAB_CONFIG_N_BITS_PROT + RAB_CONFIG_N_BITS_PORT + RAB_CONFIG_N_BITS_DATE + RAB_CONFIG_N_BITS_ACP + \
            RAB_CONFIG_N_BITS_LVL,                                                                           \
          RAB_CONFIG_N_BITS_DATE))

#define RAB_UPDATE_GET_ELEM(elem_mask, request) (elem_mask = BF_GET(request, 0, RAB_UPDATE_N_BITS_ELEM))
#define RAB_UPDATE_GET_TYPE(type, request) (type = BF_GET(request, RAB_UPDATE_N_BITS_ELEM, RAB_UPDATE_N_BITS_TYPE))

/*
 * Type Definitions - Shared between kernel and user space
 */

// RAB
typedef struct {
  unsigned short id;
  unsigned short n_elements;
  unsigned long rab_stripe_elem_user_addr; // user-space addr of stripe element array
} RabStripeReqUser;

typedef enum {
  inout = 0,
  in = 1,
  out = 2,
} ElemType;

typedef struct {
  unsigned char id;
  ElemType type;
  unsigned char flags;
  unsigned max_stripe_size_b;
  unsigned n_stripes;
  unsigned long stripe_addr_start; // user-space addr of addr_start array
  unsigned long stripe_addr_end; // user-space addr of addr_end array
} RabStripeElemUser;

// PROFILING
typedef struct {
  int valid;
  unsigned long long host_clk_start;
  unsigned long long host_clk_finish;
  unsigned long long host_time_start;
  unsigned long long host_time_finish;
  unsigned long long accel_clk_start;
  unsigned long long accel_clk_finish;
} ProfileCluster;

typedef struct {
  unsigned long long host_cur_clk;
  unsigned long long host_cur_time;
  ProfileCluster clusters[MAX_CLUSTERS];
} ProfileInfo;

// ENUMS
typedef enum { MH_NONE, MH_HOST_RAB, MH_HOST_SMMU, MH_ACCEL } MissHandlingMode;
typedef enum { MBOX_OFF, MBOX_DRIVER, MBOX_USER } MailboxMode;

/* IOCTLS
 *
 * When defining a new IOCTL command, append a macro definition to the list below, using the
 * consecutively following command number, and increase the `PULP_IOC_NR_MAX` macro.
 */
#define PULP_IOCTL_MAGIC 'p'
#define PULP_IOC_NR_MIN 0xAC
#define PULP_IOC_NR_MAX 0xC0

#define PULP_IOCTL_CTRL_RESET _IOW(PULP_IOCTL_MAGIC, 0xAC, unsigned) // value
#define PULP_IOCTL_CTRL_START _IOW(PULP_IOCTL_MAGIC, 0xAD, unsigned) // value
#define PULP_IOCTL_CTRL_STOP _IOW(PULP_IOCTL_MAGIC, 0xAE, unsigned) // value
#define PULP_IOCTL_CTRL_WAIT _IOW(PULP_IOCTL_MAGIC, 0xAF, unsigned) // value

#define PULP_IOCTL_CTRL_SET_FREQ _IOW(PULP_IOCTL_MAGIC, 0xB0, unsigned) // value

#define PULP_IOCTL_VM_SET_MH_MODE _IOW(PULP_IOCTL_MAGIC, 0xB1, unsigned) // ptr
#define PULP_IOCTL_VM_GET_MH_MODE _IOR(PULP_IOCTL_MAGIC, 0xB2, MissHandlingMode *)

#define PULP_IOCTL_RAB_REQ _IOW(PULP_IOCTL_MAGIC, 0xB3, unsigned) // ptr
#define PULP_IOCTL_RAB_FREE _IOW(PULP_IOCTL_MAGIC, 0xB4, unsigned) // value

#define PULP_IOCTL_RAB_REQ_STRIPED _IOW(PULP_IOCTL_MAGIC, 0xB5, unsigned) // ptr
#define PULP_IOCTL_RAB_FREE_STRIPED _IOW(PULP_IOCTL_MAGIC, 0xB6, unsigned) // value

#define PULP_IOCTL_MBOX_SET_MODE _IOW(PULP_IOCTL_MAGIC, 0xB7, MailboxMode)
#define PULP_IOCTL_MBOX_GET_MODE _IOW(PULP_IOCTL_MAGIC, 0xB8, MailboxMode *)
#define PULP_IOCTL_MBOX_CLEAR _IO(PULP_IOCTL_MAGIC, 0xB9)

#define PULP_IOCTL_DMA_XFER_ASYNC _IOW(PULP_IOCTL_MAGIC, 0xBB, unsigned) // ptr
#define PULP_IOCTL_DMA_XFER_WAIT _IOW(PULP_IOCTL_MAGIC, 0xBC, unsigned) // ptr

#define PULP_IOCTL_RAB_AX_LOG_ENA _IO(PULP_IOCTL_MAGIC, 0xBD)
#define PULP_IOCTL_RAB_AX_LOG_DIS _IO(PULP_IOCTL_MAGIC, 0xBE)
#define PULP_IOCTL_RAB_AX_LOG_READ _IOW(PULP_IOCTL_MAGIC, 0xBF, unsigned) // ptr

#define PULP_IOCTL_INFO_PROFILE _IOR(PULP_IOCTL_MAGIC, 0xC0, ProfileInfo)

#endif
