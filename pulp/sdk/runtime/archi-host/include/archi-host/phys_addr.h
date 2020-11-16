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

/**
 * Unified Interface to Architecture-Dependent Handling of Physical Addresses
 */

#ifndef __ARCHI_HOST_PHYS_ADDR_H__
#define __ARCHI_HOST_PHYS_ADDR_H__

#include "archi/pulp.h"     // HOST_ARCH

#ifndef HOST_ARCH
    #error "Define HOST_ARCH!"
#endif
#if HOST_ARCH == ARM64
    #include "archi-host/arm64/phys_addr.h"
#elif HOST_ARCH == ARM
    #include "archi-host/arm/phys_addr.h"
#elif HOST_ARCH == RISCV64
    #include "archi-host/riscv64/phys_addr.h"
#else
    #error "Unknown host architecture!"
#endif

/**
 * Length of the hex-formatted string of a physical address, including the base prefix and the
 * terminating null character
 *
 * PHYS_ADDR_STRLEN
 */

/**
 * Copy a physical address.
 *
 * @param   dst Pointer to which the physical address shall be copied.
 * @param   src Pointer from which the physical address shall be copied.
 *
 * @return  0 on success; negative value with an errno on errors.
 */
extern inline int copy_phys_addr(volatile phys_addr_t* const dst,
        const volatile phys_addr_t* const src);

/**
 * Print a physical address to standard output.
 *
 * @param   addr    Pointer to the physical address to be printed.
 *
 * @return  0 on success; negative value with an errno on errors.
 */
int print_phys_addr(const phys_addr_t* const addr);

/**
 * Write a physical address to a character string buffer.
 *
 * @param   strbuf  Pointer to the pre-allocated character string to write to.
 * @param   addr    Pointer to the physical address to be printed.
 *
 * @return  The number of characters written to `strbuf` (not counting the terminating null
 *          character); negative value with an errno on errors.
 */
int sprint_phys_addr(char* const strbuf, const phys_addr_t* const addr);

/**
 * Print a list of physical addresses to standard output.
 *
 * @param   begin       Pointer to the first address in the list.
 * @param   end         Pointer to the next address after the last address in the list.
 * @param   filter_fn   Pointer to a function that takes a physical address and returns 1 if the
 *                      address shall be printed; or NULL if list values shall not be filtered.
 * @param   label       String with which list values shall be labeled.
 *
 * @return  The number of printed values (non-negative); negative value with an errno on errors.
 */
int print_phys_addr_list(const phys_addr_t* const begin, const phys_addr_t* const end,
        int (*filter_fn)(const phys_addr_t* const), char* label);

#endif
