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

#include "archi-host/virt_addr.h"

#include <errno.h>
#include <inttypes.h>       // printf() identifiers

#include "rt/rt_alloc.h"    // rt_alloc(), rt_free()
#include "stdio.h"          // printf(), sprintf()

int sprint_virt_addr(char* const strbuf, const virt_addr_t* const addr)
{
    return sprintf(strbuf, "0x%08" PRIx32, *addr);
}

int print_virt_addr(const virt_addr_t* const addr)
{
    const size_t buf_size = sizeof(char) * VIRT_ADDR_STRLEN;
    char* const buf = rt_alloc(RT_ALLOC_CL_DATA, buf_size);
    if (buf == NULL)
        return -ENOMEM;
    sprint_virt_addr(buf, addr);
    printf("%s", buf);
    rt_free(RT_ALLOC_CL_DATA, buf, buf_size);
    return 0;
}
