/*
* Copyright (C) 2018 ETH Zurich and University of Bologna
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

#ifndef __HERO_API_H__
#define __HERO_API_H__

#include <stdbool.h>
#include <stdint.h>

// Error codes that are relevant from this library.  Names and values inspired by (but not
// guaranteed to be consistent with) the Linux kernel.
#define HERO_ENOMEM     12
#define HERO_EBUSY      16
#define HERO_ENODEV     19
#define HERO_EINVAL     22
#define HERO_EOVERFLOW  75
#define HERO_EALREADY  114

// If LLVM, use our address space support, otherwise fall back to bit-compatible
// data types.
#if defined(__llvm__)
#  define DEVICE_VOID_PTR __device void*
#  define HOST_VOID_PTR __host void*
#  define DEVICE_PTR __device int32_t*
#  define HOST_PTR __host int32_t*
#  define DEVICE_PTR_CONST __device int32_t* const
#  define HOST_PTR_CONST __host int32_t* const
#  define CONST_DEVICE_PTR_CONST __device const int32_t* const
#  define CONST_HOST_PTR_CONST __host const int32_t* const
#else
#  ifdef __PULP__
#    define HOST_VOID_PTR uint64_t
#    define DEVICE_VOID_PTR void *
#    define HOST_PTR uint64_t
#    define DEVICE_PTR unsigned int *
#    define HOST_PTR_CONST const uint64_t
#    define DEVICE_PTR_CONST unsigned int * const
#    define CONST_HOST_PTR_CONST const uint64_t
#    define CONST_DEVICE_PTR_CONST const unsigned int * const
#  else
#    define HOST_VOID_PTR void *
#    define DEVICE_VOID_PTR uint32_t
#    define HOST_PTR int32_t *
#    define DEVICE_PTR uint32_t
#    define HOST_PTR_CONST int32_t * const
#    define DEVICE_PTR_CONST const uint32_t
#    define CONST_HOST_PTR_CONST const int32_t * const
#    define CONST_DEVICE_PTR_CONST const uint32_t
#  endif
#endif

#define BIGPULP_SVM     (0)
#define BIGPULP_MEMCPY  (1)
#define HOST            (2)

#define HERO_L1_DATA __attribute__((section(".data_l1")))
#define HERO_L1_BSS __attribute__((section(".bss_l1")))

struct hero_dma_job {
  bool active;
  uint32_t loc;
  uint64_t ext;
  uint32_t len;
  bool ext2loc;
  uint16_t counter_mask;
};

#if defined(__llvm__)
typedef __device struct hero_dma_job* hero_dma_job_t;
#else
typedef struct hero_dma_job* hero_dma_job_t;
#endif

//!@}

/** @name DMA functions
 *
 * @{
 */

/** Used by PULP to perform a non-blocking memcpy using the DMA engine from the cluster-internal L1
    scratchpad memory to cluster-external memory (L1 of another cluster, L2, SVM).

    Resolved to a blocking memcpy() for the host.

  \param   dst  The destination address to which the data shall be copied.
  \param   src  The source address from which the data shall be copied.
  \param   size The amount of data that shall be copied in Bytes.

  \return  DMA job ID; This MUST be used to call hero_dma_wait to wait for the
           completion of this transfer before data is used or control passed to
           host. Not calling the wait function exactly once per transfer
           initiated with async can entail undefined behavior.
 */
hero_dma_job_t hero_memcpy_host2dev_async(DEVICE_VOID_PTR dst,
                                          const HOST_VOID_PTR src,
                                          uint32_t size);
hero_dma_job_t hero_memcpy_dev2host_async(HOST_VOID_PTR dst,
                                          const DEVICE_VOID_PTR src,
                                          uint32_t size);

/** Used by PULP to perform a blocking memcpy using the DMA engine from the cluster-internal L1
    scratchpad memory to cluster-external memory (L1 of another cluster, L2, SVM).

    Resolved to a blocking memcpy() for the host.

  \param   dst  The destination address to which the data shall be copied.
  \param   src  The source address from which the data shall be copied.
  \param   size The amount of data that shall be copied in Bytes.
 */
void hero_memcpy_host2dev(DEVICE_VOID_PTR dst, const HOST_VOID_PTR src,
                          uint32_t size);
void hero_memcpy_dev2host(HOST_VOID_PTR dst, const DEVICE_VOID_PTR src,
                          uint32_t size);

/** Used by PULP to wait for a previously issued memcpy/DMA transfer to finish.

    Resolved to nothing for the host.

  \param   id   The DMA job ID previously obtained from hero_dma_memcpy_async().
 */
void hero_dma_wait(hero_dma_job_t id);

//!@}

/** @name Memory management functions
 *
 * @{
 */

/** Used by PULP to allocate a chunk of memory inside the cluster-internal L1 scratchpad memory.

    Resolved to a malloc() for the host.

  \param   size The amount of memory to be allocated Bytes.

  \return  A pointer to the allocated memory chunk; NULL is returned in case the memory chunk could
           not be allocated.
 */
DEVICE_VOID_PTR hero_l1malloc(int32_t size);

/** Used by PULP to allocate a chunk of memory inside the shared L2 scratchpad memory.

    Resolved to a malloc() for the host.

  \param   size The amount of memory to be allocated Bytes.

  \return  A pointer to the allocated memory chunk; NULL is returned in case the memory chunk could
           not be allocated.
 */
DEVICE_VOID_PTR hero_l2malloc(int32_t size);

/** Used by PULP for allocation in shared L3 memory. Useful for debugging / simulation.

    Resolves to a malloc() on the host.

    NOTE: Cannot be combined with usage of L3 memory from the host
    NOTE: Every address can be allocated only once on the accelerator

    \param   size The amount of memory to be allocated Bytes.

    \return  A pointer to the allocated memory chunk; NULL is returned in case the memory chunk could
    not be allocated.
*/
HOST_VOID_PTR hero_l3malloc(int32_t size);


/** Used by PULP to free a chunk of memory inside the shared L1 scratchpad memory.

    Resolved to a free() for the host.

  \param   a The start address of the chunk to be freed.
 */
void hero_l1free(DEVICE_VOID_PTR a);

/** Used by PULP to free a chunk of memory inside the shared L2 scratchpad memory.

    Resolved to a free() for the host.

  \param   a The start address of the chunk to be freed.
 */
void hero_l2free(DEVICE_VOID_PTR a);

/** Frees memory in the shared L3 memory.

    NOTE: This function is not required to aything at the moment

    \param   a The start address of the chunk to be freed.
*/
void hero_l3free(HOST_VOID_PTR a);


//!@}

/** @name PULP runtime functions
 *
 * @{
 */

/** Get the physical ID of the core that executes the function.

  \return  The core ID.
 */
int32_t hero_rt_core_id(void);

/** Get clock counter
 */
int32_t hero_get_clk_counter(void);

/** @name Performance Measurement API
 *
 * @{
 */

/** Performance Measurement Events
 */
typedef enum {
  /// Number of clock cycles for a core.  Cannot be used as an indication of wall-clock time due to
  /// clock gating.
  hero_perf_event_cycle,
  /// Number of instructions retired by a core.
  hero_perf_event_instr_retired,
  /// Number of loads by a core.  Misaligned accesses are counted twice.
  hero_perf_event_load,
  /// Number of stores by a core.  Misaligned accesses are counted twice.
  hero_perf_event_store,
  /// Number of loads from non-local memory by a core.  Misaligned accesses are counted twice.
  hero_perf_event_load_external,
  /// Number of stores to non-local memory by a core.  Misaligned accesses are counted twice.
  hero_perf_event_store_external
} hero_perf_event_t;

/** Initialize the performance measurement library and hardware counters for a specific core.
 *
 *  This function MUST be called before any other `hero_perf_*` functions are called on a core!
 *  That is, you must call this function on every core on which you want to call `hero_perf_*`
 *  functions.
 *
 *  \return 0 on success;
 *          -HERO_ENOMEM if memory allocation failed.
 */
int hero_perf_init(void);

/** Terminate the performance library and free any resources it has taken.
 *
 *  After this function has been called, `hero_perf_init` MUST be called before any other
 *  `hero_perf_*` function (with the same conditions as `hero_perf_init`).
 */
void hero_perf_term(void);

/** Allocate a counter for an event.
 *
 *  This function allocates a free hardware counter, assigns the event to the counter, and resets
 *  the counter.
 *
 *  \return 0 on success;
 *          -HERO_EBUSY if there are no free counters available;
 *          -HERO_ENODEV if the event is not supported by the hardware;
 *          -HERO_EALREADY if a counter is already allocated for the event.
 */
int hero_perf_alloc(hero_perf_event_t event);

/** Deallocate a counter for an event.
 *
 *  \return 0 on success;
 *          -HERO_EALREADY if no counter had been allocated for the event.
 */
int hero_perf_dealloc(hero_perf_event_t event);

/** Reset the counter for an event.
 *
 *  This does not disable the counter if it was enabled.
 *
 *  \return 0 on success;
 *          -HERO_EINVAL if no counter is allocated for this event.
 */
int hero_perf_reset(hero_perf_event_t event);

/** Reset all counters.
 */
void hero_perf_reset_all(void);

/** Pause counting an event for which a counter has been allocated.
 *
 *  \return 0 on success;
 *          -HERO_EINVAL if no counter is allocated for this event.
 */
int hero_perf_pause(hero_perf_event_t event);

/** Pause counting all events.
 *
 *  This function is designed to pause all counters as promptly and closely together as possible.
 *  It takes the first of the following actions that is supported by the hardware:
 *  - Stop all allocated counters together.
 *  - Stop all counters together.
 *  - Stop each allocated counter, one after another.
 */
void hero_perf_pause_all(void);

/** Continue counting an event for which a counter has been allocated.
 *
 *  \return Same as `hero_perf_pause`.
 */
int hero_perf_continue(hero_perf_event_t event);

/** Continue counting all allocated events.
 */
void hero_perf_continue_all(void);

/** Read the counter value for an event.
 *
 *  \return >=0 counter value on success;
 *          -HERO_EINVAL if no counter is allocated for this event;
 *          -HERO_EOVERFLOW if the counter overflowed.
 */
int64_t hero_perf_read(hero_perf_event_t event);

//!@}


//FIXME: hero_rt_info();
//FIXME: hero_rt_error();

//!@}

/** @name PULP L1 Atomic Operations
 *
 * This API provides atomic transactions on 32-bit unsigned integers (for the
 * maximum and minimum operations, signed variants exist).  Each function
 * atomically executes the operation in its name on the memory pointed to by
 * `ptr` and the provided `val` and returns the original value in memory.
 *
 * NOTE: These functions are only defined for operation on the PULP L1.
 *
 *  @{
 */

int32_t  hero_atomic_swap  (DEVICE_PTR_CONST ptr, const int32_t  val);
int32_t  hero_atomic_add   (DEVICE_PTR_CONST ptr, const int32_t  val);
int32_t  hero_atomic_and   (DEVICE_PTR_CONST ptr, const int32_t  val);
int32_t  hero_atomic_or    (DEVICE_PTR_CONST ptr, const int32_t  val);
int32_t  hero_atomic_xor   (DEVICE_PTR_CONST ptr, const int32_t  val);
int32_t  hero_atomic_max   (DEVICE_PTR_CONST ptr, const int32_t  val);
uint32_t hero_atomic_maxu  (DEVICE_PTR_CONST ptr, const uint32_t val);
int32_t  hero_atomic_min   (DEVICE_PTR_CONST ptr, const int32_t  val);
uint32_t hero_atomic_minu  (DEVICE_PTR_CONST ptr, const uint32_t val);

//!@}
#endif
