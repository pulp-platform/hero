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

#include "archi-host/arm64/pgtable_dbg.h"

#include "archi-host/arm64/pgtable_hwdef.h"
#include "archi-host/phys_addr.h"

#include "stdio.h"

int print_pgd_values(const phys_addr_t* const pgd_bptr)
{
    return print_phys_addr_list(pgd_bptr, pgd_bptr + PTRS_PER_PGD, &pgd_val_is_pmd_addr, "PGD");
}
