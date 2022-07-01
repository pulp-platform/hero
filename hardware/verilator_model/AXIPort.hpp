// Copyright 2020 ETH Zurich
// 
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     http://www.apache.org/licenses/LICENSE-2.0
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#pragma once
#include <stdint.h>
#include <queue>

#define PASTER(x, y) x##_##y
#define EVALUATOR(x, y) PASTER(x, y)
#define NAME(fun) EVALUATOR(fun, VARIABLE)

#define AXI_MASTER_PORT_ASSIGN(SRC, SRC_PREFIX, DST)                          \
    {                                                                         \
        (DST)->aw_addr = &((SRC)->EVALUATOR(SRC_PREFIX, aw_addr_i));          \
        (DST)->aw_prot = &((SRC)->EVALUATOR(SRC_PREFIX, aw_prot_i));          \
        (DST)->aw_region = &((SRC)->EVALUATOR(SRC_PREFIX, aw_region_i));      \
        (DST)->aw_len = &((SRC)->EVALUATOR(SRC_PREFIX, aw_len_i));            \
        (DST)->aw_size = &((SRC)->EVALUATOR(SRC_PREFIX, aw_size_i));          \
        (DST)->aw_burst = &((SRC)->EVALUATOR(SRC_PREFIX, aw_burst_i));        \
        (DST)->aw_lock = &((SRC)->EVALUATOR(SRC_PREFIX, aw_lock_i));          \
        (DST)->aw_atop = &((SRC)->EVALUATOR(SRC_PREFIX, aw_atop_i));          \
        (DST)->aw_cache = &((SRC)->EVALUATOR(SRC_PREFIX, aw_cache_i));        \
        (DST)->aw_qos = &((SRC)->EVALUATOR(SRC_PREFIX, aw_qos_i));            \
        (DST)->aw_id = &((SRC)->EVALUATOR(SRC_PREFIX, aw_id_i));              \
        (DST)->aw_user = &((SRC)->EVALUATOR(SRC_PREFIX, aw_user_i));          \
        (DST)->aw_valid = &((SRC)->EVALUATOR(SRC_PREFIX, aw_valid_i));        \
        (DST)->aw_ready = &((SRC)->EVALUATOR(SRC_PREFIX, aw_ready_o));        \
                                                                              \
        (DST)->ar_addr = &((SRC)->EVALUATOR(SRC_PREFIX, ar_addr_i));          \
        (DST)->ar_prot = &((SRC)->EVALUATOR(SRC_PREFIX, ar_prot_i));          \
        (DST)->ar_region = &((SRC)->EVALUATOR(SRC_PREFIX, ar_region_i));      \
        (DST)->ar_len = &((SRC)->EVALUATOR(SRC_PREFIX, ar_len_i));            \
        (DST)->ar_size = &((SRC)->EVALUATOR(SRC_PREFIX, ar_size_i));          \
        (DST)->ar_burst = &((SRC)->EVALUATOR(SRC_PREFIX, ar_burst_i));        \
        (DST)->ar_lock = &((SRC)->EVALUATOR(SRC_PREFIX, ar_lock_i));          \
        (DST)->ar_cache = &((SRC)->EVALUATOR(SRC_PREFIX, ar_cache_i));        \
        (DST)->ar_qos = &((SRC)->EVALUATOR(SRC_PREFIX, ar_qos_i));            \
        (DST)->ar_id = &((SRC)->EVALUATOR(SRC_PREFIX, ar_id_i));              \
        (DST)->ar_user = &((SRC)->EVALUATOR(SRC_PREFIX, ar_user_i));          \
        (DST)->ar_valid = &((SRC)->EVALUATOR(SRC_PREFIX, ar_valid_i));        \
        (DST)->ar_ready = &((SRC)->EVALUATOR(SRC_PREFIX, ar_ready_o));        \
                                                                              \
        (DST)->w_data = (uint8_t *)&((SRC)->EVALUATOR(SRC_PREFIX, w_data_i)); \
        (DST)->w_strb = &((SRC)->EVALUATOR(SRC_PREFIX, w_strb_i));            \
        (DST)->w_user = &((SRC)->EVALUATOR(SRC_PREFIX, w_user_i));            \
        (DST)->w_last = &((SRC)->EVALUATOR(SRC_PREFIX, w_last_i));            \
        (DST)->w_valid = &((SRC)->EVALUATOR(SRC_PREFIX, w_valid_i));          \
        (DST)->w_ready = &((SRC)->EVALUATOR(SRC_PREFIX, w_ready_o));          \
                                                                              \
        (DST)->r_data = (uint8_t *)&((SRC)->EVALUATOR(SRC_PREFIX, r_data_o)); \
        (DST)->r_resp = &((SRC)->EVALUATOR(SRC_PREFIX, r_resp_o));            \
        (DST)->r_last = &((SRC)->EVALUATOR(SRC_PREFIX, r_last_o));            \
        (DST)->r_id = &((SRC)->EVALUATOR(SRC_PREFIX, r_id_o));                \
        (DST)->r_user = &((SRC)->EVALUATOR(SRC_PREFIX, r_user_o));            \
        (DST)->r_valid = &((SRC)->EVALUATOR(SRC_PREFIX, r_valid_o));          \
        (DST)->r_ready = &((SRC)->EVALUATOR(SRC_PREFIX, r_ready_i));          \
                                                                              \
        (DST)->b_resp = &((SRC)->EVALUATOR(SRC_PREFIX, b_resp_o));            \
        (DST)->b_id = &((SRC)->EVALUATOR(SRC_PREFIX, b_id_o));                \
        (DST)->b_user = &((SRC)->EVALUATOR(SRC_PREFIX, b_user_o));            \
        (DST)->b_valid = &((SRC)->EVALUATOR(SRC_PREFIX, b_valid_o));          \
        (DST)->b_ready = &((SRC)->EVALUATOR(SRC_PREFIX, b_ready_i));          \
    }


#define AXI_SLAVE_PORT_ASSIGN(SRC, SRC_PREFIX, DST)                           \
    {                                                                         \
        (DST)->aw_addr = &((SRC)->EVALUATOR(SRC_PREFIX, aw_addr_o));          \
        (DST)->aw_prot = &((SRC)->EVALUATOR(SRC_PREFIX, aw_prot_o));          \
        (DST)->aw_region = &((SRC)->EVALUATOR(SRC_PREFIX, aw_region_o));      \
        (DST)->aw_len = &((SRC)->EVALUATOR(SRC_PREFIX, aw_len_o));            \
        (DST)->aw_size = &((SRC)->EVALUATOR(SRC_PREFIX, aw_size_o));          \
        (DST)->aw_burst = &((SRC)->EVALUATOR(SRC_PREFIX, aw_burst_o));        \
        (DST)->aw_lock = &((SRC)->EVALUATOR(SRC_PREFIX, aw_lock_o));          \
        (DST)->aw_atop = &((SRC)->EVALUATOR(SRC_PREFIX, aw_atop_o));          \
        (DST)->aw_cache = &((SRC)->EVALUATOR(SRC_PREFIX, aw_cache_o));        \
        (DST)->aw_qos = &((SRC)->EVALUATOR(SRC_PREFIX, aw_qos_o));            \
        (DST)->aw_id = &((SRC)->EVALUATOR(SRC_PREFIX, aw_id_o));              \
        (DST)->aw_user = &((SRC)->EVALUATOR(SRC_PREFIX, aw_user_o));          \
        (DST)->aw_valid = &((SRC)->EVALUATOR(SRC_PREFIX, aw_valid_o));        \
        (DST)->aw_ready = &((SRC)->EVALUATOR(SRC_PREFIX, aw_ready_i));        \
                                                                              \
        (DST)->ar_addr = &((SRC)->EVALUATOR(SRC_PREFIX, ar_addr_o));          \
        (DST)->ar_prot = &((SRC)->EVALUATOR(SRC_PREFIX, ar_prot_o));          \
        (DST)->ar_region = &((SRC)->EVALUATOR(SRC_PREFIX, ar_region_o));      \
        (DST)->ar_len = &((SRC)->EVALUATOR(SRC_PREFIX, ar_len_o));            \
        (DST)->ar_size = &((SRC)->EVALUATOR(SRC_PREFIX, ar_size_o));          \
        (DST)->ar_burst = &((SRC)->EVALUATOR(SRC_PREFIX, ar_burst_o));        \
        (DST)->ar_lock = &((SRC)->EVALUATOR(SRC_PREFIX, ar_lock_o));          \
        (DST)->ar_cache = &((SRC)->EVALUATOR(SRC_PREFIX, ar_cache_o));        \
        (DST)->ar_qos = &((SRC)->EVALUATOR(SRC_PREFIX, ar_qos_o));            \
        (DST)->ar_id = &((SRC)->EVALUATOR(SRC_PREFIX, ar_id_o));              \
        (DST)->ar_user = &((SRC)->EVALUATOR(SRC_PREFIX, ar_user_o));          \
        (DST)->ar_valid = &((SRC)->EVALUATOR(SRC_PREFIX, ar_valid_o));        \
        (DST)->ar_ready = &((SRC)->EVALUATOR(SRC_PREFIX, ar_ready_i));        \
                                                                              \
        (DST)->w_data = (uint8_t *)&((SRC)->EVALUATOR(SRC_PREFIX, w_data_o)); \
        (DST)->w_strb = &((SRC)->EVALUATOR(SRC_PREFIX, w_strb_o));            \
        (DST)->w_user = &((SRC)->EVALUATOR(SRC_PREFIX, w_user_o));            \
        (DST)->w_last = &((SRC)->EVALUATOR(SRC_PREFIX, w_last_o));            \
        (DST)->w_valid = &((SRC)->EVALUATOR(SRC_PREFIX, w_valid_o));          \
        (DST)->w_ready = &((SRC)->EVALUATOR(SRC_PREFIX, w_ready_i));          \
                                                                              \
        (DST)->r_data = (uint8_t *)&((SRC)->EVALUATOR(SRC_PREFIX, r_data_i)); \
        (DST)->r_resp = &((SRC)->EVALUATOR(SRC_PREFIX, r_resp_i));            \
        (DST)->r_last = &((SRC)->EVALUATOR(SRC_PREFIX, r_last_i));            \
        (DST)->r_id = &((SRC)->EVALUATOR(SRC_PREFIX, r_id_i));                \
        (DST)->r_user = &((SRC)->EVALUATOR(SRC_PREFIX, r_user_i));            \
        (DST)->r_valid = &((SRC)->EVALUATOR(SRC_PREFIX, r_valid_i));          \
        (DST)->r_ready = &((SRC)->EVALUATOR(SRC_PREFIX, r_ready_o));          \
                                                                              \
        (DST)->b_resp = &((SRC)->EVALUATOR(SRC_PREFIX, b_resp_i));            \
        (DST)->b_id = &((SRC)->EVALUATOR(SRC_PREFIX, b_id_i));                \
        (DST)->b_user = &((SRC)->EVALUATOR(SRC_PREFIX, b_user_i));            \
        (DST)->b_valid = &((SRC)->EVALUATOR(SRC_PREFIX, b_valid_i));          \
        (DST)->b_ready = &((SRC)->EVALUATOR(SRC_PREFIX, b_ready_o));          \
    }

#define AXI_BURST_FIXED 0
#define AXI_BURST_INCR 1
#define AXI_BURST_WRAP 2

#define AXI_RESP_OKAY 0
#define AXI_RESP_EXOKAY 1
#define AXI_RESP_SLVERR 2
#define AXI_RESP_DECERR 3

// data width
#define AXI_DW 512

// strobe width = number of bytes in beat
#define AXI_SW (AXI_DW / 8)


namespace KLAS_SIM {

template<typename AW_T, typename STRB_T>
class AXIPort
{
public:
    typedef AW_T axi_addr_t;
    typedef STRB_T axi_strb_t;
    typedef uint8_t axi_prot_t;
    typedef uint8_t axi_region_t;
    typedef uint8_t axi_len_t;
    typedef uint8_t axi_size_t;
    typedef uint8_t axi_burst_t;
    typedef uint8_t axi_lock_t;
    typedef uint8_t axi_atop_t;
    typedef uint8_t axi_cache_t;
    typedef uint8_t axi_qos_t;
    typedef uint8_t axi_id_t;
    typedef uint8_t axi_user_t;

public:
    axi_addr_t *aw_addr;
    axi_prot_t *aw_prot;
    axi_region_t *aw_region;
    axi_len_t *aw_len;
    axi_size_t *aw_size;
    axi_burst_t *aw_burst;
    axi_lock_t *aw_lock;
    axi_atop_t *aw_atop;
    axi_cache_t *aw_cache;
    axi_qos_t *aw_qos;
    axi_id_t *aw_id;
    axi_user_t *aw_user;
    uint8_t *aw_valid;
    uint8_t *aw_ready;

    axi_addr_t *ar_addr;
    axi_prot_t *ar_prot;
    axi_region_t *ar_region;
    axi_len_t *ar_len;
    axi_size_t *ar_size;
    axi_burst_t *ar_burst;
    axi_lock_t *ar_lock;
    axi_cache_t *ar_cache;
    axi_qos_t *ar_qos;
    axi_id_t *ar_id;
    axi_user_t *ar_user;
    uint8_t *ar_valid;
    uint8_t *ar_ready;

    uint8_t *w_data;
    axi_strb_t *w_strb;
    axi_user_t *w_user;
    uint8_t *w_last;
    uint8_t *w_valid;
    uint8_t *w_ready;

    uint8_t *r_data;
    uint8_t *r_resp;
    uint8_t *r_last;
    axi_id_t *r_id;
    axi_user_t *r_user;
    uint8_t *r_valid;
    uint8_t *r_ready;

    uint8_t *b_resp;
    axi_id_t *b_id;
    axi_user_t *b_user;
    uint8_t *b_valid;
    uint8_t *b_ready;
};

}
