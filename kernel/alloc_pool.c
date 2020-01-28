/*
 * Copyright (C) 2019 ETH Zurich, University of Bologna
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

#include "pulp.h"
#include <string.h>
#include <stdio.h>

#if defined(ARCHI_HAS_L1)
pos_alloc_t pos_alloc_l1[ARCHI_NB_CLUSTER];
#endif

#if defined(ARCHI_HAS_FC_TCDM)
pos_alloc_t pos_alloc_fc_tcdm;
#endif

#if defined(ARCHI_HAS_L2)
pos_alloc_t pos_alloc_l2[POS_NB_ALLOC_L2];
#endif

#ifdef CONFIG_ALLOC_L2_PWD_NB_BANKS
static uint32_t pos_alloc_account_0[CONFIG_ALLOC_L2_PWD_NB_BANKS];
static uint32_t pos_alloc_account_1[CONFIG_ALLOC_L2_PWD_NB_BANKS];
#endif

#if defined(ARCHI_HAS_FC_TCDM)
static inline pos_alloc_t *get_fc_alloc() { return &pos_alloc_fc_tcdm; }
#else
static inline pos_alloc_t *get_fc_alloc() { return &pos_alloc_l2[0]; }
#endif



void pos_allocs_init()
{

#if defined(ARCHI_HAS_L2)
#if defined(ARCHI_HAS_L2_MULTI)

    //pos_trace(//pos_trace_INIT, "Initializing L2 private bank0 allocator (base: 0x%8x, size: 0x%8x)\n", (int)pos_l2_priv0_base(), pos_l2_priv0_size());
    pos_alloc_init(&pos_alloc_l2[0], pos_l2_priv0_base(), pos_l2_priv0_size());

    //pos_trace(//pos_trace_INIT, "Initializing L2 private bank1 allocator (base: 0x%8x, size: 0x%8x)\n", (int)pos_l2_priv1_base(), pos_l2_priv1_size());
    pos_alloc_init(&pos_alloc_l2[1], pos_l2_priv1_base(), pos_l2_priv1_size());

    //pos_trace(//pos_trace_INIT, "Initializing L2 shared banks allocator (base: 0x%8x, size: 0x%8x)\n", (int)pos_l2_shared_base(), pos_l2_shared_size());
    pos_alloc_init(&pos_alloc_l2[2], pos_l2_shared_base(), pos_l2_shared_size());

#ifdef CONFIG_ALLOC_L2_PWD_NB_BANKS
    pos_alloc_l2[2].track_pwd = 1;
    pos_alloc_l2[2].pwd_count = pos_alloc_account_0;
    pos_alloc_l2[2].ret_count = pos_alloc_account_0;
    for (int i=0; i<CONFIG_ALLOC_L2_PWD_NB_BANKS; i++)
    {
        pos_alloc_l2[2].pwd_count[i] = 0;
        pos_alloc_l2[2].ret_count[i] = 0;
    }
    pos_alloc_l2[2].bank_size_log2 = CONFIG_ALLOC_L2_PWD_BANK_SIZE_LOG2;
    pos_alloc_l2[2].first_bank_addr = ARCHI_L2_SHARED_ADDR;
    pos_alloc_account_free(&pos_alloc_l2[2], pos_l2_shared_base() - sizeof(pos_alloc_chunk_t), pos_l2_shared_size() + sizeof(pos_alloc_chunk_t));
#endif
#else
  //pos_trace(//pos_trace_INIT, "Initializing L2 allocator (base: 0x%8x, size: 0x%8x)\n", (int)pos_l2_base(), pos_l2_size());
    pos_alloc_init(&pos_alloc_l2[0], pos_l2_base(), pos_l2_size());
#endif
#endif

#if defined(ARCHI_HAS_FC_TCDM)
  //pos_trace(//pos_trace_INIT, "Initializing FC TCDM allocator (base: 0x%8x, size: 0x%8x)\n", (int)pos_fc_tcdm_base(), pos_fc_tcdm_size());
    pos_alloc_init(&pos_alloc_fc_tcdm, pos_fc_tcdm_base(), pos_fc_tcdm_size());
#endif
}



#if defined(ARCHI_HAS_L1)
void alloc_init_l1(int cid)
{
  pos_alloc_init(&pos_alloc_l1[cid], pos_l1_base(cid), pos_l1_size(cid));
}
#endif



void *pi_l2_malloc(int size)
{
    return pos_alloc(&pos_alloc_l2[0], size);
}

void pi_l2_free(void *_chunk, int size)
{
    return pos_free(&pos_alloc_l2[0], _chunk, size);
}

#if defined(ARCHI_HAS_FC_TCDM)
void *pi_fc_tcdm_malloc(int size)
{
    return pos_alloc(&pos_alloc_fc_tcdm, size);
}

void pi_fc_tcdm_free(void *_chunk, int size)
{
    return pos_free(&pos_alloc_fc_tcdm, _chunk, size);
}

#endif