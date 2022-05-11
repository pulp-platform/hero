/*
 * This file is part of the Snitch device driver.
 *
 * Copyright (C) 2022 ETH Zurich, University of Bologna
 *
 * Author: Noah Huetter <huettern@iis.ee.ethz.ch>
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

#ifndef _SNITCH_H
#define _SNITCH_H

/**
 * @brief When reading from the snitch driver /dev/snitch of size sizeof(struct sn_cluster_info)
 * this struct is populated and returned to user space
 * @compute_num: Number of compute cores in the cluster
 * @dm_num: Number of data mover cores in the cluster
 * @cluster_idx: Cluster index in a multi-cluster system
 * @quadrant_idx: Quadrant index in a multi-quadrant system
 * @l3_size: Size of the reserved L3 memory
 * @l1_size: Size of the TCDM address space
 * @l3_paddr: L3 physical base address
 * @l1_paddr: L1 physical base address
 * @clint_base: Physical address of clint from devicetree
 */
struct sn_cluster_info {
  uint32_t compute_num;
  uint32_t dm_num;
  uint32_t cluster_idx;
  uint32_t quadrant_idx;
  size_t l3_size;
  size_t l1_size;
  size_t periph_size;
  void *l3_paddr;
  void *l1_paddr;
  uint64_t clint_base;
};

/**
 * Macros to calculate the base address for mmap'ing regions to user space. Must be a multple of
 * PAGE_SHIFT
 */
#define SNITCH_MMAP_L3 (0 * sysconf(_SC_PAGE_SIZE))
#define SNITCH_MMAP_TCDM (1 * sysconf(_SC_PAGE_SIZE))

/**
 * IOCTL
 */

#define SNIOC_MAGIC 's'

struct snios_reg {
  uint32_t off;
  uint32_t val;
};

enum AxiTlbFlags { AXI_TLB_VALID = 0x01, AXI_TLB_RO = 0x02 };
enum AxiTlbLoc { AXI_TLB_NARROW = 1, AXI_TLB_WIDE = 2 };
struct axi_tlb_entry {
  enum AxiTlbLoc loc;
  enum AxiTlbFlags flags;
  uint64_t idx;
  uint64_t first;
  uint64_t last;
  uint64_t base;
};

/**
 * @brief set options of the snitch cluster. See below for options encoding
 *
 */
#define SNIOC_SET_OPTIONS _IOW(SNIOC_MAGIC, 0, char *)
/**
 * @brief Write to scratch registers. Pass `struct snios_reg` containing the register offset and
 * value
 *
 */
#define SNIOS_SCRATCH_W _IOW(SNIOC_MAGIC, 1, struct snios_reg)
/**
 * @brief Read from scratch registers. Pass `struct snios_reg` containing the register offset and
 * value is returned in the sturct
 *
 */
#define SNIOS_SCRATCH_R _IOWR(SNIOC_MAGIC, 2, struct snios_reg)
/**
 * @brief Read isolation bits for quadrant passed by argument. Return by value, 4 bit field of
 * isolated register
 *
 */
#define SNIOS_READ_ISOLATION _IOR(SNIOC_MAGIC, 3, char *)

/**
 * @brief Set bits in the CLINT SW-interrupt register. Pass struct snios_reg with register offset in
 * `reg` and value in `val`.
 *
 */
#define SNIOS_SET_IPI _IOR(SNIOC_MAGIC, 4, struct snios_reg)

/**
 * @brief Clear bits in the CLINT SW-interrupt register. Pass struct snios_reg with register offset
 * in `reg` and value in `val` (set bits in `val` will be cleared in clint).
 *
 */
#define SNIOS_CLEAR_IPI _IOR(SNIOC_MAGIC, 5, struct snios_reg)

/**
 * @brief Get bits in the CLINT SW-interrupt register. Pass struct snios_reg with register offset in
 * `reg` and value is written to `val`
 *
 */
#define SNIOS_GET_IPI _IOWR(SNIOC_MAGIC, 6, struct snios_reg)

/**
 * @brief Does a simple `fence` to flush the data-cache (cva6 specific, might not work on all
 * architectures)
 *
 */
#define SNIOS_FLUSH _IO(SNIOC_MAGIC, 7)
/**
 * @brief Write a TLB entry with the contents of the argument struct
 *
 */
#define SNIOS_WRITE_TLB_ENTRY _IOR(SNIOC_MAGIC, 8, struct axi_tlb_entry)
/**
 * @brief Read a TLB entry to the argument struct
 *
 */
#define SNIOS_READ_TLB_ENTRY _IOW(SNIOC_MAGIC, 9, struct axi_tlb_entry)

// Values for SNIOC_SET_OPTIONS
#define SNIOS_DEISOLATE 0x0001 /* Isolate the cluster */
#define SNIOS_ISOLATE 0x0002   /* De-isolate the cluster */

#endif
