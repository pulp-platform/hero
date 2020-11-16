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

#include "archi-host/phys_addr.h"

#include <errno.h>

#include "rt/rt_alloc.h"
#include "stddef.h"
#include "stdio.h"

int print_phys_addr(const phys_addr_t* const addr)
{
    const size_t buf_size = sizeof(char) * PHYS_ADDR_STRLEN;
    char* const buf = rt_alloc(RT_ALLOC_CL_DATA, buf_size);
    if (buf == NULL)
        return -ENOMEM;
    sprint_phys_addr(buf, addr);
    printf("%s", buf);
    rt_free(RT_ALLOC_CL_DATA, buf, buf_size);
    return 0;
}

int print_phys_addr_list(const phys_addr_t* const begin, const phys_addr_t* const end,
        int (*filter_fn)(const phys_addr_t* const), char* label)
{
    unsigned i = 0, n_printed = 0;
    for (const phys_addr_t* rptr = begin; rptr < end; ++rptr, ++i) {

        phys_addr_t value;
        int ret = copy_phys_addr(&value, rptr);
        if (ret < 0)
            return ret;

        if (filter_fn != NULL && (*filter_fn)(&value) != 1)
            continue;

        printf("%s[%04u]: ", label, i);
        print_phys_addr(&value);
        printf("\n");

        ++n_printed;

    }

    return n_printed;
}
