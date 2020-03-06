/*
 * Copyright (C) 2018 ETH Zurich and University of Bologna
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

#ifndef __CPU_ISS_RV32A_HPP
#define __CPU_ISS_RV32A_HPP

#include "iss_core.hpp"
#include "isa_lib/int.h"
#include "isa_lib/macros.h"


static inline iss_insn_t *lr_w_exec(iss_t *iss, iss_insn_t *insn)
{
  iss_lsu_amo(iss, insn, REG_GET(0), 4, REG_OUT(0), 0, vp::io_req_amo_e::LR);
  return insn->next;
}

static inline iss_insn_t *sc_w_exec(iss_t *iss, iss_insn_t *insn)
{
  iss_lsu_amo(iss, insn, REG_GET(0), 4, REG_OUT(0), REG_GET(1), vp::io_req_amo_e::SC);
  return insn->next;
}

static inline iss_insn_t *amoswap_w_exec(iss_t *iss, iss_insn_t *insn)
{
  iss_lsu_amo(iss, insn, REG_GET(0), 4, REG_OUT(0), REG_GET(1), vp::io_req_amo_e::AMO_SWAP);
  return insn->next;
}

static inline iss_insn_t *amoadd_w_exec(iss_t *iss, iss_insn_t *insn)
{
  iss_lsu_amo(iss, insn, REG_GET(0), 4, REG_OUT(0), REG_GET(1), vp::io_req_amo_e::AMO_ADD);
  return insn->next;
}

static inline iss_insn_t *amoxor_w_exec(iss_t *iss, iss_insn_t *insn)
{
  iss_lsu_amo(iss, insn, REG_GET(0), 4, REG_OUT(0), REG_GET(1), vp::io_req_amo_e::AMO_XOR);
  return insn->next;
}

static inline iss_insn_t *amoand_w_exec(iss_t *iss, iss_insn_t *insn)
{
  iss_lsu_amo(iss, insn, REG_GET(0), 4, REG_OUT(0), REG_GET(1), vp::io_req_amo_e::AMO_AND);
  return insn->next;
}

static inline iss_insn_t *amoor_w_exec(iss_t *iss, iss_insn_t *insn)
{
  iss_lsu_amo(iss, insn, REG_GET(0), 4, REG_OUT(0), REG_GET(1), vp::io_req_amo_e::AMO_OR);
  return insn->next;
}

static inline iss_insn_t *amomin_w_exec(iss_t *iss, iss_insn_t *insn)
{
  iss_lsu_amo(iss, insn, REG_GET(0), 4, REG_OUT(0), REG_GET(1), vp::io_req_amo_e::AMO_MIN);
  return insn->next;
}

static inline iss_insn_t *amomax_w_exec(iss_t *iss, iss_insn_t *insn)
{
  iss_lsu_amo(iss, insn, REG_GET(0), 4, REG_OUT(0), REG_GET(1), vp::io_req_amo_e::AMO_MAX);
  return insn->next;
}

static inline iss_insn_t *amominu_w_exec(iss_t *iss, iss_insn_t *insn)
{
  iss_lsu_amo(iss, insn, REG_GET(0), 4, REG_OUT(0), REG_GET(1), vp::io_req_amo_e::AMO_MINU);
  return insn->next;
}

static inline iss_insn_t *amomaxu_w_exec(iss_t *iss, iss_insn_t *insn)
{
  iss_lsu_amo(iss, insn, REG_GET(0), 4, REG_OUT(0), REG_GET(1), vp::io_req_amo_e::AMO_MAXU);
  return insn->next;
}

#endif
