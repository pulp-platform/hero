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
#include "pulp_dma.h"
#include "pulp_mem.h"

int pulp_dma_chan_req(struct dma_chan **chan, int chan_id)
{
  dma_cap_mask_t mask;
  dmafilter_param_t filter;

  dma_cap_zero(mask);
  dma_cap_set(DMA_SLAVE, mask);

  filter.driver_name = "dma-pl330";
  filter.chan_id = chan_id;

  if (DEBUG_LEVEL_DMA > 1)
    filter.debug_print = 1;
  else
    filter.debug_print = 0;

  *chan = dma_request_channel(mask, dmafilter_fn, &filter);

  if (!(*chan)) {
    printk(KERN_WARNING "PULP - DMA: Channel request for %s[%d] failed.\n", filter.driver_name, filter.chan_id);
    return -EBUSY;
  }

  return 0;
}

void pulp_dma_chan_clean(struct dma_chan *chan)
{
  dmaengine_terminate_all(chan);

  dma_release_channel(chan);
}

int pulp_dma_xfer_prep(struct dma_async_tx_descriptor **desc, struct dma_chan **chan, unsigned addr_dst, unsigned addr_src,
                       unsigned size_b, bool last)
{
  unsigned flags;

  // set the interrupt flag for last transaction
  if (!last)
    flags = 0;
  else
    flags = DMA_PREP_INTERRUPT;

  if (DEBUG_LEVEL_DMA > 1) {
    printk("PULP - DMA: New Segment.\n");
    printk("PULP - DMA: Source address      = %#x \n", addr_src);
    printk("PULP - DMA: Destination address = %#x \n", addr_dst);
    printk("PULP - DMA: Transfer size       = %#x \n", size_b);
  }

  // prepare the transaction
  *desc = (*chan)->device->device_prep_dma_memcpy(*chan, addr_dst, addr_src, size_b, flags);
  if (*desc == NULL) {
    printk("PULP - DMA: Transfer preparation failed.\n");
    return -EBUSY;
  }

  return 0;
}

void pulp_dma_xfer_cleanup(DmaCleanup *pulp_dma_cleanup)
{
#ifndef PROFILE_DMA
  struct dma_async_tx_descriptor **descs;
#endif

  struct page **pages;
  unsigned n_pages;

  int i;

  if (DEBUG_LEVEL_DMA > 0)
    printk("PULP - DMA: Transfer finished, cleanup called.\n");

  // finally unlock remapped pages
  pages = pulp_dma_cleanup->pages;
  n_pages = pulp_dma_cleanup->n_pages;

  for (i = 0; i < n_pages; i++) {
    if (!PageReserved(pages[i]))
      SetPageDirty(pages[i]);
    put_page(pages[i]);
  }

  // free pages struct pointer array
  kfree(pages);

#ifndef PROFILE_DMA
  // free transaction descriptors array
  descs = pulp_dma_cleanup->descs;
  kfree(descs);
#endif

  // signal to user-space runtime?
}

bool dmafilter_fn(struct dma_chan *chan, void *param)
{
  struct dma_device *device = chan->device;
  struct device *dev = device->dev;
  struct device_driver *driver = dev->driver;
  dmafilter_param_t *filter = param;
  int priv = *((int *)(chan->private));

  if (filter->debug_print)
    printk("name=%s,chan_id=%d,private=%x\n", driver->name, chan->chan_id, priv);

  if (filter->driver_name && strcmp(driver->name, filter->driver_name))
    return false;

  if ((filter->chan_id >= 0) && (chan->chan_id != filter->chan_id))
    return false;

  return (true);
}

int pulp_dma_xfer_async(struct dma_chan **dma_chan, DmaCleanup *dma_cleanup, unsigned addr_l3, unsigned addr_pulp,
                        unsigned size_b, unsigned char dma_cmd)
{
  int i, j, err;

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

  // descriptor and addresses
  struct dma_async_tx_descriptor **descs;
  unsigned addr_src, addr_dst;

  if (DEBUG_LEVEL_DMA > 0) {
    printk(KERN_INFO "PULP: New DMA request:\n");
    printk(KERN_INFO "PULP: addr_l3   = %#x.\n", addr_l3);
    printk(KERN_INFO "PULP: addr_pulp = %#x.\n", addr_pulp);
    printk(KERN_INFO "PULP: size_b = %#x.\n", size_b);
    printk(KERN_INFO "PULP: dma_cmd = %#x.\n", dma_cmd);
  }

  // number of pages
  len = pulp_mem_get_num_pages(addr_l3, size_b);

  // get and lock user-space pages
  err = pulp_mem_get_user_pages(&pages, addr_l3, len, dma_cmd);
  if (err) {
    printk(KERN_WARNING "PULP: Locking of user-space pages failed.\n");
    return err;
  }

  // virtual to physcial address translation + segmentation
  n_segments = pulp_mem_map_sg(&addr_start_vec, &addr_end_vec, &addr_offset_vec, &page_idxs_start, &page_idxs_end, &pages,
                               len, addr_l3, addr_l3 + size_b);
  if (n_segments < 1) {
    printk(KERN_WARNING "PULP: Virtual to physical address translation failed.\n");
    return n_segments;
  }

  // allocate memory to hold the transaction descriptors
  descs =
    (struct dma_async_tx_descriptor **)kmalloc((size_t)(n_segments * sizeof(struct dma_async_tx_descriptor *)), GFP_KERNEL);

  // prepare cleanup
  dma_cleanup[dma_cmd].descs = descs;
  dma_cleanup[dma_cmd].pages = pages;
  dma_cleanup[dma_cmd].n_pages = len;

  /*
   *  setup the transfers
   */
  size_b = 0;
  for (i = 0; i < n_segments; i++) {
    addr_pulp += size_b;

    if (dma_cmd) { // PULP -> L3 // not yet tested
      addr_src = addr_pulp;
      addr_dst = addr_offset_vec[i];
    } else { // L3 -> PULP
      addr_src = addr_offset_vec[i];
      addr_dst = addr_pulp;
    }
    size_b = addr_end_vec[i] - addr_start_vec[i];

    // flush caches
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

    // prepare the transfers, fill the descriptors
    err = pulp_dma_xfer_prep(&descs[i], &dma_chan[dma_cmd], addr_dst, addr_src, size_b, (i == n_segments - 1));
    if (err) {
      printk(KERN_WARNING "PULP: Could not setup DMA transfer.\n");
      return err;
    }

    // set callback parameters for last transaction
    if (i == (n_segments - 1)) {
      descs[i]->callback = (dma_async_tx_callback)pulp_dma_xfer_cleanup;
      descs[i]->callback_param = &dma_cleanup[dma_cmd];
    }

    // submit the transaction
    descs[i]->cookie = dmaengine_submit(descs[i]);
  }
  if (DEBUG_LEVEL_DMA > 1)
    printk(KERN_INFO "PULP: DMA transactions for %i segments submitted.\n", n_segments);

#ifdef PROFILE_DMA
  time_dma_start = ktime_get();
#endif
  // issue pending DMA requests and wait for callback notification
  dma_async_issue_pending(dma_chan[dma_cmd]);

  if (DEBUG_LEVEL_DMA > 1)
    printk(KERN_INFO "PULP: Pending DMA transactions issued.\n");

#ifdef PROFILE_DMA
  // wait for finish
  for (j = 0; j < 100000; j++) {
    ret = dma_async_is_tx_complete(pulp_dma_chan[dma_cmd], descs[n_segments - 1]->cookie, NULL, NULL);
    if (!ret)
      break;
    udelay(10);
  }
  // free transaction descriptors array
  kfree(descs);

  // time measurement
  time_dma_end = ktime_get();
  time_dma_acc = ktime_us_delta(time_dma_end, time_dma_start);

  printk("PULP - DMA: size = %d [bytes]\n", request[2] & 0x7FFFFFFF);
  printk("PULP - DMA: time = %d [us]\n", time_dma_acc);
#endif

  return 0;
}
