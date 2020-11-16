/*
 * Copyright (C) 2017 ETH Zurich and University of Bologna
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

#ifndef __VMM_H__
#define __VMM_H__

#include "archi-host/phys_addr.h"
#include "archi-host/virt_addr.h"

#include <stddef.h>     // size_t

/**
 * Translate a virtual address to its page physical address.
 *
 * @param   virt_addr       Virtual address to be translated.
 * @param   page_phys_addr  Pointer through which the physical address of the page shall be
 *                          returned.
 * @param   page_rdonly     Pointer to a byte that shall be set to `1` if the page is read-only.
 *
 * @return  0 if the translation was successful; negative value with an errno on errors (in this
 *          case, the value of `page_phys_addr` after the function returns is undefined).
 */
int virt_addr_to_page_phys_addr(const virt_addr_t virt_addr,
        phys_addr_t* const page_phys_addr, unsigned char* const page_rdonly);

/**
 * Add a mapping for the page corresponding to a virtual address.
 *
 * For performance reasons, this function does not check if the page is already mapped!  Thus, the
 * *caller* must make sure that this function is not called on pages that are already mapped.
 *
 * @param   virt_ptr    A pointer in the virtual address space.
 *
 * @return  0 on success; negative value with an errno on errors.  After the function returns
 *          sucessfully, addresses on the same page as `virt_ptr` can be accessed.
 */
int map_page(const void* const virt_ptr);

/**
 * Add mappings for all pages in a range of virtual addresses.
 *
 * For performance reasons, this function does not check if the pages are already mapped!  Thus, the
 * *caller* must make sure that this function is not called on pages that are already mapped.
 *
 * @param   virt_ptr    A pointer that has the value of the first address in the address range.
 * @param   n_bytes     The number of bytes to be mapped.
 *
 * @return  0 on success; negative value with an errno on errors.  -ENOMEM is returned in case the
 *          mappings would exceed the capacity of RAB.  After the function returns successfully,
 *          addresses in the specified range can be accessed.
 */
int map_pages(const void* const virt_ptr, const size_t n_bytes);

/**
 * Remove the mapping for the page corresponding to the virtual address.
 *
 * @param   virt_ptr    A pointer in the virtual address space.
 *
 * @return  0 on success; negative value with an errno on errors.  -ENOENT is returned in case no
 *          mapping for the virtual address could be found.  After the function returns
 *          successfully, addresses on the same page as `virt_ptr` must no longer be accessed.
 */
int unmap_page(const void* const virt_ptr);

/**
 * Handle all outstanding RAB misses (if there are any).
 *
 * @return  0 on success; negative value with an errno on errors.  -ENOENT is returned in case no
 *          misses were outstanding.
 */
int handle_rab_misses();

/**
 * Reset all relevant VMM data structures statically allocated in L1 memory.
 *
 * This function must be called in case the L1 memory is not loaded.
 */
void reset_vmm();

#endif
