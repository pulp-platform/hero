/*
 * Copyright (C) 2018 ETH Zurich, University of Bologna
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


#ifndef __ARCHI_CHIPS_BIGPULP_MEMORY_MAP_H__
#define __ARCHI_CHIPS_BIGPULP_MEMORY_MAP_H__



/*
 * SOC PERIPHERALS
 */

#define ARCHI_SOC_PERIPHERALS_ADDR    0x1A100000


#define ARCHI_UART_OFFSET             0x00002000
#define ARCHI_APB_SOC_CTRL_OFFSET     0x00003000
#define ARCHI_STDOUT_OFFSET           0x0000F000
#define ARCHI_RAB_CFG_OFFSET          0x00030000

#define ARCHI_UART_ADDR              ( ARCHI_SOC_PERIPHERALS_ADDR + ARCHI_UART_OFFSET )
#define ARCHI_APB_SOC_CTRL_ADDR      ( ARCHI_SOC_PERIPHERALS_ADDR + ARCHI_APB_SOC_CTRL_OFFSET )
#define ARCHI_STDOUT_ADDR            ( ARCHI_SOC_PERIPHERALS_ADDR + ARCHI_STDOUT_OFFSET )
#if PULP_CHIP == CHIP_HERO_URANIA
  // HACK: Ariane does not map the RAB directly so access it done through the host
  #define ARCHI_RAB_CFG_ADDR            0x30000000
#else
  #define ARCHI_RAB_CFG_ADDR           ( ARCHI_SOC_PERIPHERALS_ADDR + ARCHI_RAB_CFG_OFFSET )
#endif
#define ARCHI_MAILBOX_BASE_ADDR       0x1B800000

/*
 * CLUSTER
 */

#define ARCHI_CLUSTER_ADDR              0x1B000000
#define ARCHI_CLUSTER_SIZE              0x00400000
#define ARCHI_CLUSTER_GLOBAL_ADDR(cid)  (0x10000000 + (cid)*ARCHI_CLUSTER_SIZE)

/*
 * CLUSTER PERIPHERALS
 */

#define ARCHI_CLUSTER_PERIPHERALS_OFFSET 0x00200000

#define ARCHI_CLUSTER_CTRL_OFFSET        0x00000000
#define ARCHI_TRYX_OFFSET                0x00000BFC
#define ARCHI_TIMER_OFFSET               0x00000400
#define ARCHI_EU_OFFSET                  0x00000800
#define ARCHI_ICACHE_CTRL_OFFSET         0x00001400

#define ARCHI_CLUSTER_PERIPHERALS_ADDR             ( ARCHI_CLUSTER_ADDR + ARCHI_CLUSTER_PERIPHERALS_OFFSET )
#define ARCHI_CLUSTER_PERIPHERALS_GLOBAL_ADDR(cid) ( ARCHI_CLUSTER_GLOBAL_ADDR(cid) + ARCHI_CLUSTER_PERIPHERALS_OFFSET )

#define ARCHI_CLUSTER_CTRL_ADDR                    ( ARCHI_CLUSTER_PERIPHERALS_ADDR + ARCHI_CLUSTER_CTRL_OFFSET )
#define ARCHI_TRYX_ADDR                            ( 0x10000000 + ARCHI_CLUSTER_PERIPHERALS_OFFSET + ARCHI_TRYX_OFFSET )
#define ARCHI_TIMER_ADDR                           ( ARCHI_CLUSTER_PERIPHERALS_ADDR + ARCHI_TIMER_OFFSET )
#define ARCHI_EU_ADDR                              ( ARCHI_CLUSTER_PERIPHERALS_ADDR + ARCHI_EU_OFFSET )
#define ARCHI_ICACHE_CTRL_ADDR                     ( ARCHI_CLUSTER_PERIPHERALS_ADDR + ARCHI_ICACHE_CTRL_OFFSET )

/*
 * CLUSTER DEMUX PERIPHERALS
 */

#define ARCHI_DEMUX_PERIPHERALS_OFFSET        0x204000

#define ARCHI_EU_DEMUX_OFFSET                 ( 0x00000 )
#define ARCHI_MCHAN_DEMUX_OFFSET              ( 0x00400 )

#define ARCHI_DEMUX_PERIPHERALS_ADDR          ( ARCHI_CLUSTER_ADDR + ARCHI_DEMUX_PERIPHERALS_OFFSET )

#define ARCHI_EU_DEMUX_ADDR                   ( ARCHI_DEMUX_PERIPHERALS_ADDR + ARCHI_EU_DEMUX_OFFSET )
#define ARCHI_MCHAN_DEMUX_ADDR                ( ARCHI_DEMUX_PERIPHERALS_ADDR + ARCHI_MCHAN_DEMUX_OFFSET )

#endif
