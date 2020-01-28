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

volatile unsigned int pos_soc_event_status[ARCHI_SOC_EVENT_NB_TOTAL/32];

extern void pos_soc_event_handler_asm();

void pos_soc_event_init()
{

#if defined(ARCHI_HAS_FC)
    // Deactivate all soc events as they are active by default
    soc_eu_eventMask_reset(SOC_FC_FIRST_MASK);
#endif

#if defined(ARCHI_HAS_FC)
    // Activate soc events handler
    //pos_irq_set_handler(ARCHI_FC_EVT_SOC_EVT, pos_soc_event_handler_asm);
    //pos_irq_mask_set(1<<ARCHI_FC_EVT_SOC_EVT);
#endif
}