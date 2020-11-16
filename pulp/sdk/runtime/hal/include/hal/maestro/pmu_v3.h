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

#ifndef __HAL_MAESTRO_PMU_V3_H__
#define __HAL_MAESTRO_PMU_V3_H__

#include "hal/pulp.h"
#include "archi/maestro/maestro_v3.h"


#define PMU_PICL_PACK(chipsel,addr) (((chipsel) << 5) | (addr))
#define PMU_DLC_PACK(state,picl) (((state) << 16) | ((picl) << 1) | 0x1); //write 0x2 at picl_reg


#define PMU_WRITE(offset, value) IP_WRITE(ARCHI_PMU_ADDR, offset, value)
#define PMU_READ(offset) IP_READ(ARCHI_PMU_ADDR, offset)


static inline void hal_pmu_state_set(unsigned int state) {
  unsigned int picl_reg = PMU_PICL_PACK(ARCHI_PMU_CS_WIU, ARCHI_PMU_WIU_IFR_0);
  unsigned int dlc_reg = PMU_DLC_PACK(state, picl_reg);
  PMU_WRITE(ARCHI_PCTRL_OFFSET, dlc_reg);
}

#endif