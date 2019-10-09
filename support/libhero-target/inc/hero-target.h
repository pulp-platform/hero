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

#include <stdio.h>
#include <stdint.h>

#define BIGPULP_SVM     (0)
#define BIGPULP_MEMCPY  (1)
#define HOST            (2)

typedef int hero_dma_job_t;

/** @name SVM-related functions
 *
 * @{
 */

/** Used by PULP to securely read from an address in SVM and block until the read completes.

    Resolved to a normal read for the host.

  \param   addr  The address that shall be read.

  \return  The data stored at that address.
 */
unsigned int hero_tryread(const unsigned int* const addr);

/** Used by PULP to try to read from a memory address without blocking in case it misses in the RAB
    and without causing a memory transaction. This function can be used to trigger the setup of a
    RAB slice in advance of a read.

    Resolved to nothing for the host.

  \param   addr  The address that shall be read-prefetched.

  \return  0 if the read would succeed (i.e., a slice in the RAB exists for this address); 1 if
           the read resulted in a RAB miss; negative value with an errno on errors.
 */
int hero_tryread_prefetch(const unsigned int* const addr);

/** Used by PULP to securely write to an address in SVM and block until the write completes.

    Resolved to a normal write for the host.

  \param   addr  The address to which data shall be written.
  \param   val   The value that shall be written.
 */
void hero_trywrite(unsigned int* const addr, const unsigned int val);

/** Used by PULP to Try to write to a memory address without blocking in case it misses in the RAB
    and without causing a memory transaction. This function can be used to trigger the setup of a
    RAB slice in advance of a write.

    Resolved to nothing for the host.

  \param   addr  The address that shall be write-prefetched.

  \return  0 if the write would succeed (i.e., a slice in the RAB exists for this address); 1 if
           the write resulted in a RAB miss; negative value with an errno on errors.
 */
int hero_trywrite_prefetch(unsigned int* const addr);

/** Used by PULP to handle all outstanding RAB misses (if there are any).

    Resolved to nothing for the host.

  \return  0 on success; negative value with an errno on errors. -ENOENT is returned in case no
           misses were outstanding.
 */
int hero_handle_rab_misses(void);

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

  \return  DMA job ID; This can be used with hero_dma_wait to wait for the completion of this transfer.
 */
hero_dma_job_t hero_dma_memcpy_async(void *dst, void *src, int size);

/** Used by PULP to perform a blocking memcpy using the DMA engine from the cluster-internal L1
    scratchpad memory to cluster-external memory (L1 of another cluster, L2, SVM).

    Resolved to a blocking memcpy() for the host.

  \param   dst  The destination address to which the data shall be copied.
  \param   src  The source address from which the data shall be copied.
  \param   size The amount of data that shall be copied in Bytes.
 */
void hero_dma_memcpy(void *dst, void *src, int size);

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
void *hero_l1malloc(int size);

/** Used by PULP to allocate a chunk of memory inside the shared L2 scratchpad memory.

    Resolved to a malloc() for the host.

  \param   size The amount of memory to be allocated Bytes.

  \return  A pointer to the allocated memory chunk; NULL is returned in case the memory chunk could
           not be allocated.
 */
void *hero_l2malloc(int size);

/** Used by PULP for allocation in shared L3 memory. Useful for debugging / simulation.

    Resolves to a malloc() on the host.

    NOTE: Cannot be combined with usage of L3 memory from the host
    NOTE: Every address can be allocated only once on the accelerator

    \param   size The amount of memory to be allocated Bytes.

    \return  A pointer to the allocated memory chunk; NULL is returned in case the memory chunk could
    not be allocated.
*/
void *hero_l3malloc(int size);


/** Used by PULP to free a chunk of memory inside the shared L1 scratchpad memory.

    Resolved to a free() for the host.

  \param   a The start address of the chunk to be freed.
 */
void hero_l1free(void * a);

/** Used by PULP to free a chunk of memory inside the shared L2 scratchpad memory.

    Resolved to a free() for the host.

  \param   a The start address of the chunk to be freed.
 */
void hero_l2free(void * a);

/** Frees memory in the shared L3 memory.

    NOTE: This function is not required to aything at the moment

    \param   a The start address of the chunk to be freed.
*/
void hero_l3free(void * a);


//!@}

/** @name PULP runtime functions
 *
 * @{
 */

/** Get the physical ID of the core that executes the function.

  \return  The core ID.
 */
int hero_rt_core_id(void);

/** Reset clock counter
 */
void hero_reset_clk_counter(void);

/** Get clock counter
 */
int hero_get_clk_counter(void);

//FIXME: hero_rt_info();
//FIXME: hero_rt_error();

//!@}

#endif
