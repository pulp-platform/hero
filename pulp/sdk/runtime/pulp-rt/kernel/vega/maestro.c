#if 1

/*
 * Copyright (C) 2018 ETH Zurich, University of Bologna and GreenWaves Technologies
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

/* 
 * Authors: Eric Flamand, GreenWaves Technologies (eric.flamand@greenwaves-technologies.com)
 *          Germain Haugou, ETH (germain.haugou@iis.ee.ethz.ch)
 */

#include "rt/rt_api.h"
#include "stdio.h"


void __rt_pmu_cluster_power_down()
{
#if 0
  //plp_trace(RT_TRACE_PMU, "Cluster power down\n");

  // Check bit 14 of bypass register to see if an external tool (like gdb) is preventing us
  // from shutting down the cluster
  if ((hal_pmu_bypass_get() >> APB_SOC_BYPASS_USER1_BIT) & 1) return;

  // Wait until cluster is not busy anymore as isolating it while
  // AXI transactions are sent would break everything
  // This part does not need to be done asynchronously as the caller is supposed to make 
  // sure the cluster is not active anymore..
  while (apb_soc_busy_get()) {
    __rt_wait_for_event(1<<ARCHI_FC_EVT_CLUSTER_NOT_BUSY);
  }

  // Block transactions from dc fifos to soc
  apb_soc_cluster_isolate_set(1);

  // Cluster clock-gating
  hal_pmu_bypass_set( (1<<ARCHI_PMU_BYPASS_ENABLE_BIT) | (1<<ARCHI_PMU_BYPASS_CLUSTER_POWER_BIT) );
  __rt_wait_for_event(1<<ARCHI_FC_EVT_CLUSTER_CG_OK);

  // Cluster shutdown
  hal_pmu_bypass_set( (1<<ARCHI_PMU_BYPASS_ENABLE_BIT) );
  __rt_wait_for_event(1<<ARCHI_FC_EVT_CLUSTER_POK);
  // We should not need to wait for power off as it is really quick but we actually do
#endif
}

void __rt_pmu_cluster_power_up()
{
  //plp_trace(RT_TRACE_PMU, "Cluster power up\n");

  hal_pmu_state_set(ARCHI_PMU_STATE_SOC_NV_CLU_NV);

  // Tell external loader (such as gdb) that the cluster is on so that it can take it
  // into account
  //hal_pmu_bypass_set( (1<<ARCHI_PMU_BYPASS_ENABLE_BIT) | (1<<ARCHI_PMU_BYPASS_CLUSTER_POWER_BIT) | (1<<ARCHI_PMU_BYPASS_CLUSTER_RESET_BIT) | (1<<ARCHI_PMU_BYPASS_CLUSTER_CLOCK_BIT) | (1 << APB_SOC_BYPASS_USER0_BIT));
}

void __rt_pmu_init()
{
}

#else

/*
 * Copyright (C) 2018 ETH Zurich, University of Bologna and GreenWaves Technologies
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

/* 
 * Authors: Eric Flamand, GreenWaves Technologies (eric.flamand@greenwaves-technologies.com)
 *          Germain Haugou, ETH (germain.haugou@iis.ee.ethz.ch)
 */

#include "rt/rt_api.h"
#include "stdio.h"
#include "hal/maestro/pmu_v2.h"

#define PMU_DLC_PCTRL_REG ARCHI_PMU_ADDR + 0x00
#define PMU_DLC_IFR_REG   ARCHI_PMU_ADDR + 0x10

#define PMU_STATE_SOC_NV     2
#define PMU_STATE_SOC_LV     3
#define PMU_STATE_SOC_CLU_NV 4
#define PMU_STATE_SOC_CLU_LV 5
#define PMU_STATE_DEEP_SLEEP 0

#define PMU_PICL_WIU  1
#define PMU_PICL_ICU0 2
#define PMU_PICL_ICU1 3
#define PMU_PICL_ICU2 4

#define PMU_WIU_ISPMR_0 0
#define PMU_WIU_ISPMR_1 1
#define PMU_WIU_IFR_0   2
#define PMU_WIU_IFR_1   3


void set_PMUState(unsigned int state) {
  pulp_write32(PMU_DLC_IFR_REG,0xFF); //clears previous interrupts
  unsigned int SetSCUInt = ((1<<state)<<16)|((PMU_PICL_WIU)<<6)|((PMU_WIU_IFR_1)<<1)|1;
  pulp_write32(PMU_DLC_PCTRL_REG,SetSCUInt);
  __rt_periph_wait_event(ARCHI_SOC_EVENT_SCU_OK, 1);
}


void __rt_pmu_cluster_power_down()
{
#if 0
  //plp_trace(RT_TRACE_PMU, "Cluster power down\n");

  // Check bit 14 of bypass register to see if an external tool (like gdb) is preventing us
  // from shutting down the cluster
  if ((hal_pmu_bypass_get() >> APB_SOC_BYPASS_USER1_BIT) & 1) return;

  // Wait until cluster is not busy anymore as isolating it while
  // AXI transactions are sent would break everything
  // This part does not need to be done asynchronously as the caller is supposed to make 
  // sure the cluster is not active anymore..
  while (apb_soc_busy_get()) {
    __rt_wait_for_event(1<<ARCHI_FC_EVT_CLUSTER_NOT_BUSY);
  }

  // Block transactions from dc fifos to soc
  apb_soc_cluster_isolate_set(1);

  // Cluster clock-gating
  hal_pmu_bypass_set( (1<<ARCHI_PMU_BYPASS_ENABLE_BIT) | (1<<ARCHI_PMU_BYPASS_CLUSTER_POWER_BIT) );
  __rt_wait_for_event(1<<ARCHI_FC_EVT_CLUSTER_CG_OK);

  // Cluster shutdown
  hal_pmu_bypass_set( (1<<ARCHI_PMU_BYPASS_ENABLE_BIT) );
  __rt_wait_for_event(1<<ARCHI_FC_EVT_CLUSTER_POK);
  // We should not need to wait for power off as it is really quick but we actually do
#endif
}

void __rt_pmu_cluster_power_up()
{
  //plp_trace(RT_TRACE_PMU, "Cluster power up\n");

  /* Turn on power, this will also clock ungate the cluster */
  set_PMUState(PMU_STATE_SOC_CLU_NV);

  // Unblock transactions from dc fifos to soc
  apb_soc_cluster_isolate_set(0);

  // Tell external loader (such as gdb) that the cluster is on so that it can take it
  // into account
  hal_pmu_bypass_set( (1<<ARCHI_PMU_BYPASS_ENABLE_BIT) | (1<<ARCHI_PMU_BYPASS_CLUSTER_POWER_BIT) | (1<<ARCHI_PMU_BYPASS_CLUSTER_RESET_BIT) | (1<<ARCHI_PMU_BYPASS_CLUSTER_CLOCK_BIT) | (1 << APB_SOC_BYPASS_USER0_BIT));
}

void __rt_pmu_init()
{
  soc_eu_fcEventMask_setEvent(ARCHI_SOC_EVENT_SCU_OK);
}

#endif
