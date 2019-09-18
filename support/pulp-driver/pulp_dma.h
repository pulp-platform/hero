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
#ifndef _PULP_DMA_H_
#define _PULP_DMA_H_

#include <linux/dmaengine.h> /* dma_cap_zero(), dma_cap_set */
#include <linux/dma-mapping.h> /* dma_alloc_coherent(),dma_free_coherent() */
#include <linux/completion.h> /* For complete(), wait_for_completion_*() */
#include <linux/mm.h> /* vm_area_struct struct, page struct, PAGE_SHIFT, page_to_phys */
#include <linux/pagemap.h> /* page_put() */
#include <linux/slab.h> /* kmalloc() */

#include "pulp_module.h"

typedef struct {
  struct dma_async_tx_descriptor **descs;
  struct page **pages;
  unsigned n_pages;
} DmaCleanup;

typedef struct {
  int chan_id; /* Set to negative to not use. */
  const char *driver_name; /* Set to NULL to not use. */
  int debug_print;
} dmafilter_param_t;

/** @name DMA channel management functions
 *
 * @{
 */

/** Request a channel of the PL330 DMA inside the Zynq PS.

  \param    chan    pointer to the dma_chan struct to use.
  \param    chan_id ID of the channel to request. 0: Host -> PULP, 1: PULP -> Host.

  \return   0 on success; negative value with an errno on errors.
 */
int pulp_dma_chan_req(struct dma_chan **chan, int chan_id);

/** Clean up a DMA channel through the Linux DMA API.

  \param    chan pointer to the dma_chan struct.
 */
void pulp_dma_chan_clean(struct dma_chan *chan);

//!@}

/** @name DMA transfer management functions
 *
 * @{
 */

/** Enqueue a new DMA transfer.

 \param     desc     pointer to the dma_async_tx_descriptor struct to fill.
 \param     chan     pointer to the dma_chan struct to use.
 \param     addr_dst physical destination address.
 \param     addr_src physical source address.
 \param     size_b   number of bytes to transfer.
 \param     last     indicates the last transfer of series, set interrupt flag.

 \return    0 on success; negative value with an errno on errors.
 */
int pulp_dma_xfer_prep(struct dma_async_tx_descriptor **desc, struct dma_chan **chan, unsigned addr_dst, unsigned addr_src,
                       unsigned size_b, bool last);

/** Clean up after a DMA transfer has finished, the callback function. Unlocks user pages and
 *  frees memory.

  \param    pulp_dma_cleanup pointer to the DmaCleanup struct.
 */
void pulp_dma_xfer_cleanup(DmaCleanup *pulp_dma_cleanup);

/** Obtain a specific channel exclusively. Used by the Linux DMA API.

 \param    chan  pointer to the dma_chan struct to use.
 \param    param pointer to the filter parameters.

 \return   true if requested channel is found; false otherwise.
 */
bool dmafilter_fn(struct dma_chan *chan, void *param);

//!@}

/** @name DMA execution functions
 *
 * @{
 */

/** Execute a asynchronous DMA transfer

    \param dma_channel array of pointer to dma channels
    \param dma_cleanup array of dma cleanup structures
    \param addr_l3 address of memory on the host L3
    \param addr_pulp address of memory on the pulp
    \param size_b number of bytes to copy
    \param dma_cmd zero to copy from pulp to l3, one to copy from l3 to pulp
*/

int pulp_dma_xfer_async(struct dma_chan **dma_chan, DmaCleanup *dma_cleanup, unsigned addr_l3, unsigned addr_pulp,
                        unsigned size_b, unsigned char dma_cmd);

//!@}

#endif /*_PULP_DMA_H_*/
