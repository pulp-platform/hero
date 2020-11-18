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
 * ARM64-Specific Definitions for Debugging the Page Table
 */

#ifndef __ARCHI_HOST_ARM64_PGTABLE_DBG_H__
#define __ARCHI_HOST_ARM64_PGTABLE_DBG_H__

#include "archi-host/arm64/phys_addr.h"

/**
 * Print the values of a PGD to standard output.
 *
 * @param   pgd_bptr    Pointer to the begin of the PGD.
 *
 * @return  The number of printed values (non-negative); negative value with an errno on errors.
 */
int print_pgd_values(const phys_addr_t* const pgd_bptr);

#endif
