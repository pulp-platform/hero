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
#ifndef _PULP_MEM_H_
#define _PULP_MEM_H_

#include <linux/module.h> /* Needed by all modules */
#include <linux/kernel.h> /* KERN_ALERT, container_of */
#include <linux/slab.h> /* kmalloc */
#include <linux/mm.h> /* vm_area_struct struct, page struct, PAGE_SHIFT, page_to_phys */
#include <linux/highmem.h> /* kmap, kunmap */

#include "pulp_module.h"

/** @name Data cache management functions
 *
 * @{
 */

/** Flush user-space memory pages. Required when PULP reads from user-space memory.

  \param    page         pointer to the page struct of user-space memory page to flush.
  \param    offset_start address offset to start flushing from.
  \param    offset_end   address offset to end flushing at.
 */
void pulp_mem_cache_flush(struct page *page, unsigned offset_start, unsigned offset_end);

/** Invalidate user-space memory pages. Required when PULP writes to user-space memory.

  \param    page         pointer to the page struct of user-space memory page to flush.
  \param    offset_start address offset to start flushing from.
  \param    offset_end   address offset to end flushing at.
 */
void pulp_mem_cache_inv(struct page *page, unsigned offset_start, unsigned offset_end);

//!@}

/** @name User-space memory functions
 *
 * @{
 */

/** Get the number of pages to remap.

  \param    addr_start start address of the mapping.
  \param    size_b     size in bytes of the mapping.

  \return   number of pages toched by the requested mapping.
 */
unsigned pulp_mem_get_num_pages(unsigned addr_start, unsigned size_b);

/** Get pointers to user-space pages' page structs of the calling process and lock the
 *  corresponding pages in memory.

 \param    pages      pointer to the pages' page structs.
 \param    addr_start virtual user-space address to start remapping from.
 \param    n_pages    number of pages to remap.
 \param    write      if non-zero, remap pages in write mode.

 \return   0 on success; negative value with an errno on errors.
 */
int pulp_mem_get_user_pages(struct page ***pages, unsigned addr_start, unsigned n_pages, unsigned write);

/** Translate user-space pages' virtual addresses into physical addresses and group them into
 *  segments of physically contiguous addresses.

  \param    addr_start_vec  pointer to array containing virtual start addresses of the segments.
  \param    addr_end_vec    pointer to array containing virtual end addresses of the segments.
  \param    addr_offset_vec pointer to array containing address offsets (physical) of the segments.
  \param    page_start_idxs pointer to array containing start indexes of the segments in pages.
  \param    page_end_idxs   pointer to array containing end indexes of the segments in pages.
  \param    pages           pointer to the pages' page structs.
  \param    n_pages         number of pages to map.
  \param    addr_start      virtual start address of the mapping.
  \param    addr_end        virtual end address of the mapping.

  \return   number of segments on success; negative value with an errno on errors.
 */
int pulp_mem_map_sg(unsigned **addr_start_vec, unsigned **addr_end_vec, unsigned long **addr_offset_vec,
                    unsigned **page_start_idxs, unsigned **page_end_idxs, struct page ***pages, unsigned n_pages,
                    unsigned addr_start, unsigned addr_end);

/** Translate user-space pages' virtual addresses into physical addresses and groups them into
 *  segments of physically contiguous addresses.

  \param    pages   pointer to the pages' page structs.
  \param    n_pages number of pages to map.

  \return   number of segments on success; negative value with an errno on errors.
 */
int pulp_mem_check_num_sg(struct page ***pages, unsigned n_pages);

/** Get the physical pageframe numbers for every virtual page.

 \param    pfn_v_vec  pointer to array containing virtual pageframe numbers.
 \param    pfn_p_vec  pointer to array containing physical pageframe numbers.
 \param    pages      pointer to the pages' page structs.
 \param    n_pages    Number of pages to translate.
 \param    addr_start virtual start address of the mapping.

 \return   0 on success; negative value with an errno on errors.
 */
int pulp_mem_l2_get_entries(unsigned **virtual_page_vec, unsigned **phy_page_vec, struct page ***pages, unsigned n_pages,
                            unsigned addr_start);

//!@}

#endif /*_PULP_MEM_H_*/
