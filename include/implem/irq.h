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

#ifndef __POS_IMPLEM_IRQ_H__
#define __POS_IMPLEM_IRQ_H__

#include "hal/pulp.h"



void pos_irq_init();

void pos_irq_set_handler(int irq, void (*handler)());



static inline void pos_irq_mask_set(unsigned int mask)
{
#if defined(__RISCV_GENERIC__)
    // Generic riscv case, e.g. Ibex
    hal_spr_read_then_set_from_reg(0x304, mask);

#elif defined(ITC_VERSION) && defined(EU_VERSION)
    // Case with ITC on FC and event unit on cluster, e.g. Wolfe
    if (hal_is_fc())
        hal_itc_enable_set(mask);
    else
        eu_irq_maskSet(mask);

#elif defined(ITC_VERSION)
    // Case with only ITC, e.g. Pulpissimo
    hal_itc_enable_set(mask);

#elif defined(EU_VERSION)
    // Case with only event unit, e.g. Gap
    eu_irq_maskSet(mask);
    // This is needed on architectures where the FC is using an event unit as we
    // use an elw instead of a wfi with interrupts disabled. The fact that the event
    // is active will make the core goes out of elw and the interrupt handler
    // will be called as soon as interrupts are enabled.
    if (hal_is_fc())
        eu_evt_maskSet(mask);
#endif
}



static inline void pos_irq_mask_clr(unsigned int mask)
{
#if defined(__RISCV_GENERIC__)
    hal_spr_read_then_clr_from_reg(0x304, mask);

#elif defined(ITC_VERSION) && defined(EU_VERSION)
    if (hal_is_fc())
        hal_itc_enable_clr(mask);
    else
        eu_irq_maskClr(mask);

#elif defined(ITC_VERSION)

    hal_itc_enable_clr(mask);

#elif defined(EU_VERSION)
    eu_irq_maskClr(mask);
    if (hal_is_fc())
        eu_evt_maskClr(mask);
#endif
}



static inline void pos_irq_clr(unsigned int mask)
{
#if defined(__RISCV_GENERIC__)
    // TODO 

#elif defined(ITC_VERSION) && defined(EU_VERSION)
    if (hal_is_fc())
        hal_itc_status_clr(mask);
    else
        eu_evt_clr(mask);

#elif defined(ITC_VERSION)
    hal_itc_status_clr(mask);

#elif defined(EU_VERSION) && EU_VERSION >= 3
    eu_evt_clr(mask);
#endif
}

static inline unsigned int pos_irq_get_fc_vector_base()
{
    if (hal_is_fc())
    {
#if defined(__RISCV_GENERIC__)
        return hal_spr_read(0x305) & ~1;
#elif defined(ARCHI_CORE_HAS_SECURITY) && !defined(ARCHI_CORE_HAS_1_10)
        return __builtin_pulp_spr_read(SR_MTVEC);
#elif defined(ARCHI_CORE_HAS_1_10)
        return __builtin_pulp_spr_read(SR_MTVEC) & ~1;
#elif defined(APB_SOC_VERSION) && APB_SOC_VERSION >= 2
        return apb_soc_bootaddr_get();
#endif
    }
    else
    {
#if defined(ARCHI_HAS_CLUSTER)
#if defined(ARCHI_CLUSTER_CTRL_ADDR)
        return plp_ctrl_bootaddr_get();
#endif
#endif
    }

    return 0;
}



static inline void pos_irq_set_fc_vector_base(unsigned int base)
{
    if (hal_is_fc())
    {
#if defined(__RISCV_GENERIC__)
        hal_spr_write(0x305, base);
#elif defined(ARCHI_CORE_HAS_SECURITY)
        __builtin_pulp_spr_write(SR_MTVEC, base);
#elif defined(ARCHI_CORE_HAS_1_10)
        __builtin_pulp_spr_write(SR_MTVEC, base | 1);
#elif defined(APB_SOC_VERSION) && APB_SOC_VERSION >= 2
        apb_soc_bootaddr_set(base);
#endif
    }
    else
    {
#if defined(ARCHI_HAS_CLUSTER)
#if defined(ARCHI_CLUSTER_CTRL_ADDR)
        plp_ctrl_bootaddr_set(base);
#endif
#endif
    }
}


static inline void pos_irq_wait_for_interrupt()
{
#if !defined(ARCHI_HAS_FC) || defined(ARCHI_HAS_FC_EU)
    eu_evt_wait();
#else
    hal_itc_wait_for_interrupt();
#endif
}



#endif
