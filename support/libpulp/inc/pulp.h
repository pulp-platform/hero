/*
 * This file is part of the PULP user-space runtime library.
 *
 * Copyright 2018 ETH Zurich, University of Bologna
 *
 * Author: Pirmin Vogel <vogelpi@iis.ee.ethz.ch>
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

#ifndef PULP_H__
#define PULP_H__

#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h> // for mmap
#include <fcntl.h>
#include <errno.h> // for error codes
#include <stdbool.h> // for bool
#include <sys/ioctl.h> // for ioctl
#include <stdlib.h> // for system
#include <unistd.h> // for usleep, access

#include <errno.h>

/*
 * Debug flags
 */
#ifndef DEBUG_LEVEL
  #define DEBUG_LEVEL 0
#endif

/*
 * Defines
 */
// Include defines shared between kernel and userspace
#include "pulp_common.h"
#include "archi/pulp.h"

/*
 * Type Definitions
 */
typedef struct {
  unsigned *v_addr;
  unsigned size;
} PulpSubDev;

typedef struct {
  int fd; // file descriptor
  PulpSubDev clusters;
  PulpSubDev soc_periph;
  PulpSubDev mbox;
  PulpSubDev l2_mem;
  PulpSubDev l3_mem;
  PulpSubDev gpio;
  PulpSubDev clking;
  PulpSubDev rab_config;
  PulpSubDev pulp_res_v_addr;
  PulpSubDev l3_mem_res_v_addr;
#if PLATFORM != JUNO
  PulpSubDev slcr;
#endif
  struct O1HeapInstance* l3_heap_mgr;
  unsigned int cluster_sel; // cluster select
  unsigned int host_clk_freq_mhz;
  unsigned int pulp_clk_freq_mhz;
} PulpDev;

// striping informationg structure
typedef struct {
  unsigned n_stripes;
  unsigned first_stripe_size_b;
  unsigned last_stripe_size_b;
  unsigned stripe_size_b;
} StripingDesc;

typedef enum {
  copy = 0x0, // no SVM, copy-based sharing using contiguous L3 memory
  svm_static = 0x1, // SVM, set up static mapping at offload time, might fail - use with caution
  svm_stripe = 0x2, // SVM, use striping (L1 only), might fail - use with caution
  svm_mh = 0x3, // SVM, use miss handling
  copy_tryx = 0x4, // no SVM, copy-based sharing using contiguous L3 memory, but let PULP do the tryx()
  svm_smmu = 0x5, // SVM, use SMMU instead of RAB
  svm_smmu_shpt = 0x6, // SVM, use SMMU, emulate sharing of user-space page table, no page faults
  custom = 0xF, // do not touch (custom marshalling)
} ShMemType;

typedef enum {
  val = 0x0, // pass by value

  ref_copy = 0x10, // pass by reference, no SVM, use contiguous L3 memory
  ref_svm_static = 0x11, // pass by reference, SVM, set up mapping at offload time
  ref_svm_stripe = 0x12, // pass by reference, SVM, set up striped mapping
  ref_svm_mh = 0x13, // pass by reference, SVM, do not set up mapping, use miss handling
  ref_copy_tryx = 0x14, // pass by reference, no SVM, use contiguous L3 memory, but to the tryx() - mapped to 0x10
  ref_custom = 0x1F, // pass by reference, do not touch (custom marshalling)
} ElemPassType;

// shared variable data structure
typedef struct {
  void *ptr; // address in host virtual memory
  void *ptr_l3_v; // host virtual address in contiguous L3 memory   - filled by runtime library based on sh_mem_ctrl
  void *ptr_l3_p; // PULP physical address in contiguous L3 memory  - filled by runtime library based on sh_mem_ctrl
  unsigned size; // size in Bytes
  ElemType type; // inout, in, out
  ShMemType sh_mem_ctrl;
  unsigned char cache_ctrl; // 0: flush caches, access through DRAM
    // 1: do not flush caches, access through caches
  unsigned char rab_lvl; // 0: first L1, L2 when full
    // 1: L1 only
    // 2: L2 only
  StripingDesc *stripe_desc; // only used if sh_mem_ctrl = 2
} DataDesc;

// task descriptor created by the compiler
typedef struct {
  int task_id; // used for RAB managment -> expiration date
  char *name;
  int n_clusters;
  int n_data;
  DataDesc *data_desc;
} TaskDesc;

/** @name Basic PULP memory access functions
 *
 * @{
 */

/** Read 32 bits from PULP.

  \param    base_addr virtual address pointer to base address
  \param    off       offset
  \param    off_type  type of the offset, 'b' = byte offset, else word offset

  \return   value read at the specified address
 */
uint32_t pulp_read32(const volatile uint32_t *base_addr, uint32_t off, char off_type);

/** Write 32 bits to PULP.

  \param    base_addr virtual address pointer to base address
  \param    off       offset
  \param    off_type  type of the offset, 'b' = byte offset, else word offset
 */
void pulp_write32(volatile uint32_t *base_addr, uint32_t off, char off_type, uint32_t value);

//!@}

/** @name Mailbox communication functions
 *
 * @{
 */

/** Read one or multiple words from the mailbox. Blocks if the mailbox does not contain enough
 *  data.

  \param    pulp    pointer to the PulpDev structure
  \param    buffer  pointer to read buffer
  \param    n_words number of words to read

  \return   0 on success; negative value with an errno on errors.
 */
int pulp_mbox_read(const PulpDev *pulp, uint32_t *buffer, size_t n_words);

/** Write one word to the mailbox. Blocks if the mailbox is full.

 \param     pulp pointer to the PulpDev structure
 \param     word word to write

 \return    0 on success; negative value with an errno on errors.
 */
int pulp_mbox_write(PulpDev *pulp, uint32_t word);

//!@}

/** @name PULP library setup functions
 *
 * @{
 */

/** Reserve the virtual address space overlapping with the physical address map of PULP as well as
 *  the contiguous L3 memory using mmap() syscalls with MAP_FIXED and MAP_ANONYMOUS.

  \param    pulp pointer to the PulpDev structure

  \return   0 on success; negative value with an errno on errors.
 */
int pulp_reserve_v_addr(PulpDev *pulp);

/** Free previously reserved virtual address space using the munmap() syscall.

  \param    pulp pointer to the PulpDev structure

  \return   0 on success; negative value with an errno on errors.
 */
int pulp_free_v_addr(const PulpDev *pulp);

/** Print information about the reserved virtual address space.

  \param    pulp pointer to the PulpDev structure
 */
void pulp_print_v_addr(PulpDev *pulp);

/** Memory map the PULP device to virtual user space using the mmap() syscall.

  \param    pulp pointer to the PulpDev structure

  \return   0 on success; negative value with an errno on errors.
 */
int pulp_mmap(PulpDev *pulp);

/** Undo the memory mapping of the PULP device to virtual user space using the munmap() syscall.

  \param    pulp pointer to the PulpDev structure

  \return   0 on success; negative value with an errno on errors.
 */
int pulp_munmap(PulpDev *pulp);

//!@}

/** @name PULP hardware setup functions
 *
 * @{
 */

/** Set the clock frequency of PULP. Blocks until the PLL inside PULP locks.

 * NOTE: Only do this at startup of PULP!

  \param    pulp         pointer to the PulpDev structure
  \param    des_freq_mhz desired clock frequency in MHz

  \return   configured frequency in MHz.
 */
int pulp_clking_set_freq(PulpDev *pulp, unsigned des_freq_mhz);

/** Measure the clock frequency of PULP. Can only be executed with the RAB configured to allow
 *  accessing the cluster peripherals. To validate the measurement, the ZYNQ_PMM needs to be loaded
 *  for accessing to the ARM clock counters.

  \param    pulp pointer to the PulpDev structure

  \return   measured clock frequency in MHz.
 */
int pulp_clking_measure_freq(PulpDev *pulp);

/** Initialize the memory mapped PULP device: disable reset and fetch enable, set up basic RAB
 *  mappings, enable mailbox interrupts, disable RAB miss interrupts, pass information to driver.

 *  NOTE: PULP needs to be mapped to memory before this function can be executed.

  \param    pulp pointer to the PulpDev structure

  \return   0 on success; negative value with an errno on errors.
 */
int pulp_init(PulpDev *pulp);

/** Reset PULP.

  \param    pulp pointer to the PulpDev structure
  \param    full type of reset: 0 for PULP reset, 1 for entire FPGA
 */
void pulp_reset(PulpDev *pulp, unsigned full);

//!@}

/** @name PULP execution control functions
 *
 * @{
 */

/** Boot PULP, i.e., load a binary and start its execution.

  \param    pulp pointer to the PulpDev structure
  \param    task pointer to the TaskDesc structure

  \return   0 on success; negative value with an errno on errors.
 */
int pulp_boot(PulpDev *pulp, const TaskDesc *task);

/** Load binaries to the start of the TCDM and the start of the L2 memory inside PULP. This
 *  function uses an mmap() system call to map the specified binaries to memory.

  \param    pulp pointer to the PulpDev structure
  \param    name pointer to the string containing the name of the application to load

  \return   0 on success; negative value with an errno on errors.
 */
int pulp_load_bin(PulpDev *pulp, const char *name);

/** Load binary to the start of the L2 memory inside PULP. This functions expects the binary to be
 *  loaded in host memory.

 \param    pulp pointer to the PulpDev structure
 \param    ptr  pointer to mem where the binary is loaded
 \param    size binary size in bytes

 \return   0 on success.
 */
int pulp_load_bin_from_mem(PulpDev *pulp, void *ptr, unsigned size);

/** Starts programm execution on PULP.

 \param    pulp pointer to the PulpDev structure
 */
void pulp_exe_start(PulpDev *pulp);

/** Stops programm execution on PULP.

 \param    pulp pointer to the PulpDev structure
 */
void pulp_exe_stop(PulpDev *pulp);

/** Polls the GPIO register for the end of computation signal for at most timeout_s seconds.

 \param    pulp      pointer to the PulpDev structure
 \param    timeout_s maximum number of seconds to wait for end of computation

 \return   0 on success; -ETIME in case of an execution timeout or -ENOSYS if EOC is not available.
 */
int pulp_exe_wait(const PulpDev *pulp, int timeout_s);

//!@}

/** @name Static RAB setup functions
 *
 * @{
 */

/** Request a RAB remapping using one or multiple TLB entries.

  \param    pulp       pointer to the PulpDev structure
  \param    addr_start (virtual) start address
  \param    size_b     size of the remapping in bytes
  \param    prot       protection flags, one bit each for write, read, and enable
  \param    port       RAB port, 0 = Host->PULP, 1 = PULP->Host
  \param    date_exp   expiration date of the mapping
  \param    date_cur   current date, used to check and replace expired entries

  \return   0 on success; negative value with an errno on errors.
 */
int pulp_rab_req(const PulpDev *pulp, unsigned addr_start, unsigned size_b, unsigned char prot, unsigned char port,
                 unsigned char date_exp, unsigned char date_cur, unsigned char use_acp, unsigned char rab_lvl);

/** Free RAB remappings.

  \param    pulp     pointer to the PulpDev structure
  \param    date_cur current date, 0 = RAB_MAX_DATE = free all slices
 */
void pulp_rab_free(const PulpDev *pulp, unsigned char date_cur);

/** Request striped RAB remappings

  \param    pulp       pointer to the PulpDev structure
  \param    task       pointer to the TaskDesc structure
  \param    pass_type  pointer to array marking the elements to pass by reference
  \param    n_elements number of striped data elements

  \return   0 on success; negative value with an errno on errors.
 */
int pulp_rab_req_striped(const PulpDev *pulp, const TaskDesc *task, ElemPassType **pass_type, int n_elements);

/** Free striped RAB remappings

  \param    pulp pointer to the PulpDev structure
 */
void pulp_rab_free_striped(const PulpDev *pulp);

//!@}

/** @name Dynamic, on-demand RAB/SMMU setup functions
 *
 * @{
 */

/** Enable handling of RAB misses by the SoC.

 *  The PULP driver function called by this function basically does two things:  First, it sets up
 *  RAB so that the page table hierarchy can be accessed from PULP.  For this, slices either for
 *  the first-level page table or for all second-level page tables are configured in RAB
 *  (definable, see parameter below). Second, the driver function disables handling of RAB misses
 *  in the Kernel driver itself and prohibits the driver to write to those slices that are now
 *  managed by the SoC.

  \param    pulp                    Pointer to the PulpDev struct.
  \param    static_2nd_lvl_slices   If 0, the driver sets up a single RAB slice for the first level
                                    of the page table; if 1, the driver sets up RAB slices for all
                                    valid second-level page tables.  The latter is not supported by
                                    all architectures.  If unsupported, the driver will fall back
                                    to the former behavior and emit a warning.

  \return  0 on success; negative value with an errno on errors. See the documentation of
           `pulp_rab_soc_mh_ena()` for particular values.
 */
int pulp_rab_soc_mh_enable(const PulpDev *pulp, const unsigned static_2nd_lvl_slices);

/** Disable handling of RAB misses by the SoC.

 *  The PULP driver function called by this function frees and deconfigures all slices used to map
 *  the initial level of the page table and hands the slices that were reserved to be managed by
 *  the SoC back to the host.

  \param    pulp Pointer to the PulpDev struct.

  \return   0 on success; negative value with an errno on errors. See the documentation of
           `pulp_rab_soc_mh_dis()` for particular values.
 */
int pulp_rab_soc_mh_disable(const PulpDev *pulp);

/** Enable handling of RAB misses by the host.

  \param    pulp       pointer to the PulpDev structure
  \param    use_acp    coherency setup, 0: non-coherent mappings, 1: coherent mappings
  \param    rav_mh_lvl TLB level, 1: use L1 TLB, 2: use L2 TLB

  \return   0 on success; negative value with an errno on errors.
 */
int pulp_rab_mh_enable(const PulpDev *pulp, unsigned char use_acp, unsigned char rab_mh_lvl);

/** Disable handling of RAB misses by the host.

  \param    pulp       pointer to the PulpDev structure

  \return   0 on success; negative value with an errno on errors.
 */
int pulp_rab_mh_disable(const PulpDev *pulp);

/** Enable SMMU for SVM.

  \param    pulp  pointer to the PulpDev structure
  \param    flags configuration for page fault handler

  \return   0 on success; negative value with an errno on errors.
 */
int pulp_smmu_enable(const PulpDev *pulp, const unsigned char flags);

/** Disable SMMU for SVM.

  \param    pulp  pointer to the PulpDev structure

  \return   0 on success; negative value with an errno on errors.
 */
int pulp_smmu_disable(const PulpDev *pulp);

//!@}

/** @name RAB logger functions
 *
 * @{
 */

/** Store the content of the RAB AX Logger to a file.

 *  This function reads the content of the RAB AX Logger from kernel space, sorts the entries
 *  according the timestamp, and writes the data into the file `rab_ax_log_%Y-%m-%d_%H-%M-%S.txt`
 *  (see `man date` for the exact meaning of the format specifiers).
 *
 *  This function must be called before freeing the RAB, otherwise the RAB free will already empty
 *  the kernel space buffers.

  \param    pulp Pointer to the PulpDev struct.

  \return   0 on success; negative value with an errno on errors.
 */
int pulp_rab_ax_log_read(const PulpDev *pulp);

/** Reads profiling information from the driver

  \param    pulp Pointer to the PulpDev struct
  \param    info Pointer to a ProfileInfo struct to write to

  \return   0 on succes; negative value with errno on errors
 */
int pulp_profile_info(const PulpDev *pulp, ProfileInfo *profile_info);

//!@}

/** @name PULP offload interface functions
 *
 * @{
 */

/** Offload a new task to PULP, set up static RAB entries and pass descriptors to PULP.

  \param    pulp pointer to the PulpDev structure
  \param    task pointer to the TaskDesc structure

  \return   0 on success; negative value with an errno on errors.
 */
int pulp_offload_out(PulpDev *pulp, TaskDesc *task);

/** Finish a task offload, clear static RAB and get back descriptors passed by value.

  \param    pulp pointer to the PulpDev structure
  \param    task pointer to the TaskDesc structure

  \return   0 on success; negative value with an errno on errors.
 */
int pulp_offload_in(PulpDev *pulp, TaskDesc *task);

/** Find out which shared data elements to pass by reference and if yes, with which type of memory
 *  sharing.

  \param    task      pointer to the TaskDesc structure
  \param    pass_type pointer to array marking the elements to pass by reference

  \return   Number of data elements to pass by reference.
 */
int pulp_offload_get_pass_type(const TaskDesc *task, ElemPassType **pass_type);

/** Set up the RAB for the offload based on the task descriptor struct.

 *  Try to reorder the shared data elements to minimize the number of entries used.

  \param    pulp      pointer to the PulpDev structure
  \param    task      pointer to the TaskDesc structure
  \param    pass_type pointer to array marking the elements to pass by reference
  \param    n_ref     number of shared data elements passed by reference

  \return   0 on success; negative value with an errno on errors.
 */
int pulp_offload_rab_setup(const PulpDev *pulp, const TaskDesc *task, ElemPassType **pass_type, int n_ref);

/** Free RAB mappings for the offload based on the task descriptor struct.

  \param    task      pointer to the TaskDesc structure
  \param    pass_type pointer to array marking the elements to pass by reference
  \param    n_ref     number of shared data elements passed by reference

  \return   0 on success.
 */
int pulp_offload_rab_free(const PulpDev *pulp, const TaskDesc *task, const ElemPassType **pass_type, int n_ref);

/** Pass the descriptors of the shared data elements to PULP.

  \param    pulp      pointer to the PulpDev structure
  \param    task      pointer to the TaskDesc structure
  \param    pass_type pointer to array marking the elements to pass by references

  \return   0 on success.
 */
int pulp_offload_pass_desc(PulpDev *pulp, const TaskDesc *task, const ElemPassType **pass_type);

/** Get back the shared data elements from PULP that were passed by value.

  \param    pulp      pointer to the PulpDev structure
  \param    task      pointer to the TaskDesc structure
  \param    pass_type pointer to array marking the elements to pass by reference

  \return   0 on success; negative value with an errno on errors.
 */
int pulp_offload_get_desc(const PulpDev *pulp, TaskDesc *task, const ElemPassType **pass_type);

/** Copy raw data elements from virtual to contiguous L3 memory and fill pointer values in data
 *  descriptor.

 *  WARNING: Pointers inside the data element are not changed.

  \param    pulp      pointer to the PulpDev structure
  \param    task      pointer to the TaskDesc structure
  \param    pass_type pointer to array marking the elements to pass by reference

  \return   0 on success; negative value with an errno on errors.
 */
int pulp_offload_l3_copy_raw_out(PulpDev *pulp, TaskDesc *task, const ElemPassType **pass_type);

/** Copy raw data elements back from contiguous L3 memory to virtual memory.

 *  WARNING: Pointers inside the data element are not changed.

  \param    pulp      pointer to the PulpDev structure
  \param    task      pointer to the TaskDesc structure
  \param    pass_type pointer to array marking the elements to pass by reference

  \return   0 on success; negative value with an errno on errors.
 */
int pulp_offload_l3_copy_raw_in(PulpDev *pulp, const TaskDesc *task, const ElemPassType **pass_type);

//!@}

/** @name Contiguous memory allocation functions
 *
 * @{
 */

/** Allocate a chunk of memory in contiguous L3.

  \param    pulp   pointer to the PulpDev structure
  \param    size_b size in Bytes of the requested chunk
  \param    p_addr pointer to store the physical address to

  \return   virtual user-space address for host
 */
uintptr_t pulp_l3_malloc(PulpDev *pulp, unsigned size_b, uintptr_t *p_addr);

/** Free memory previously allocated in contiguous L3.

 \param    pulp   pointer to the PulpDev structure
 \param    v_addr pointer to unsigned containing the virtual address
 \param    p_addr pointer to unsigned containing the physical address

 */
void pulp_l3_free(PulpDev *pulp, uintptr_t v_addr, uintptr_t p_addr);

//!@}

/** @name Host DMA functions
 *
 * @{
 */

/** Setup a DMA transfer using the Host DMA engine

 \param    pulp      pointer to the PulpDev structure
 \param    addr_l3   virtual address in host's L3
 \param    addr_pulp physical address in PULP, so far, only L2 tested
 \param    size_b    size in bytes
 \param    host_read 0: Host -> PULP, 1: PULP -> Host (not tested)

 \return   0 on success; negative value with an errno on errors.
 */
int pulp_dma_xfer(const PulpDev *pulp, uintptr_t addr_l3, uintptr_t addr_pulp, size_t size_b, int host_read);

//!@}

/** @name Legacy functions - do not use these any longer.
 *
 * @{
 */

/** Offload an OpenMP task to PULP and setup the RAB

 *  NOTE: Do not use this function any longer. Currently, it is used only by
 *  profile_rab_striping. It may be removed soon.

 \param    pulp pointer to the PulpDev structure
 \param    task pointer to the TaskDesc structure

 \return   0 on success; negative value with an errno on errors.
 */
int pulp_omp_offload_task(PulpDev *pulp, TaskDesc *task);

//!@}

#endif // PULP_H__
