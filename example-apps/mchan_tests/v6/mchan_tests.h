#ifndef MCHAN_H
#define MCHAN_H

#include "pulp.h"

#define TX 0
#define RX 1
#define INC 1
#define FIX 0
#define LIN 0
#define TWD 1

#define MCHAN_COMMAND_QUEUE (ARCHI_MCHAN_DEMUX_ADDR + PLP_DMA_QUEUE_OFFSET)
#define MCHAN_STATUS_REGISTER (ARCHI_MCHAN_DEMUX_ADDR + PLP_DMA_STATUS_OFFSET)

// TEMPORARY FIX DAVIDE
#define PE_MCHAN_COMMAND_QUEUE 0x10201800
#define PE_MCHAN_STATUS_REGISTER 0x10201804

#ifdef ARCHI_MCHAN_EXT_OFFSET
#define PE_MCHAN_COMMAND_QUEUE (ARCHI_CLUSTER_PERIPHERALS_GLOBAL_ADDR(0) + ARCHI_MCHAN_EXT_OFFSET + PLP_DMA_QUEUE_OFFSET)
#define PE_MCHAN_STATUS_REGISTER (ARCHI_CLUSTER_PERIPHERALS_GLOBAL_ADDR(0) + ARCHI_MCHAN_EXT_OFFSET + PLP_DMA_STATUS_OFFSET)
#endif

#define FC_DMA_EVENT 8
#define CL_DMA_EVENT 22

static inline int mchan_alloc(){
  return *(volatile int*) MCHAN_COMMAND_QUEUE;
}

static inline void mchan_transfer(unsigned int len, char type, char incr, char twd, char ele, char ile, char ble, unsigned int ext_addr, unsigned int tcdm_addr, unsigned short int count, unsigned short int stride)
{
 *(volatile int*) MCHAN_COMMAND_QUEUE = len | (type<<PLP_DMA_TYPE_BIT) | ( incr<<PLP_DMA_INCR_BIT) | (twd <<PLP_DMA_2D_BIT) | (ele<<PLP_DMA_ELE_BIT) | (ile <<PLP_DMA_ILE_BIT) | (ble <<PLP_DMA_BLE_BIT);
 *(volatile int*) MCHAN_COMMAND_QUEUE = tcdm_addr;
 *(volatile int*) MCHAN_COMMAND_QUEUE = ext_addr;
 
 if (twd == 1) *(volatile int*) MCHAN_COMMAND_QUEUE = count | (stride << 16);
}

static inline void mchan_barrier(int id) {
  while(((*(volatile int*)(MCHAN_STATUS_REGISTER)) >> id ) & 0x1 ) {
    eu_evt_maskWaitAndClr(1<<FC_DMA_EVENT);
 }
}

static inline void mchan_free(int id) {
  *(volatile int*) MCHAN_STATUS_REGISTER = 0x1 << id;
}

#ifdef PE_MCHAN_COMMAND_QUEUE
static inline int pe_mchan_alloc(){
  return *(volatile int*) PE_MCHAN_COMMAND_QUEUE;
}

static inline void pe_mchan_transfer(unsigned int len, char type, char incr, char twd, char ele, char ile, char ble, unsigned int ext_addr, unsigned int tcdm_addr, unsigned short int count, unsigned short int stride)
{
 *(volatile int*) PE_MCHAN_COMMAND_QUEUE = len | (type<<PLP_DMA_TYPE_BIT) | ( incr<<PLP_DMA_INCR_BIT) | (twd <<PLP_DMA_2D_BIT) | (ele<<PLP_DMA_ELE_BIT) | (ile <<PLP_DMA_ILE_BIT) | (ble <<PLP_DMA_BLE_BIT);
 *(volatile int*) PE_MCHAN_COMMAND_QUEUE = tcdm_addr;
 *(volatile int*) PE_MCHAN_COMMAND_QUEUE = ext_addr;
 
 if (twd == 1) *(volatile int*) PE_MCHAN_COMMAND_QUEUE = count | (stride << 16);
}

static inline void pe_mchan_barrier(int id) {
  while(((*(volatile int*)(PE_MCHAN_STATUS_REGISTER)) >> id ) & 0x1 ) {
    if (plp_isFc()) {
#if PULP_CHIP != CHIP_GAP     
      hal_itc_wait_for_event_noirq(1<<FC_DMA_EVENT);
#else 
      eu_evt_maskWaitAndClr(1<<FC_DMA_EVENT);
#endif      
    }
    else eu_evt_maskWaitAndClr(1<<CL_DMA_EVENT);
  };
}

static inline void pe_mchan_free(int id) {
  *(volatile int*) PE_MCHAN_STATUS_REGISTER = 0x1 << id;
}

#endif

#endif
