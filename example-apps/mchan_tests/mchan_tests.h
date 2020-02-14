#ifndef MCHAN_TEST_H
#define MCHAN_TEST_H

#include "pulp.h"

#define TX 0
#define RX 1
#define INC 1
#define FIX 0
#define LIN 0
#define TWD 1

#define MCHAN_COMMAND_QUEUE    0x10201800
#define MCHAN_STATUS_REGISTER  0x10201804

// TEMPORARY FIX DAVIDE
#define PLP_DMA_2D_TCDM_BIT 22

#define PE_MCHAN_COMMAND_QUEUE   0x10201C00
#define PE_MCHAN_STATUS_REGISTER 0x10201C04

#define PLP_DMA_TYPE_BIT  0x00000011
#define PLP_DMA_INCR_BIT 0x00000012
#define PLP_DMA_2D_BIT 0x00000013
#define PLP_DMA_ELE_BIT 0x00000014
#define PLP_DMA_ILE_BIT 0x00000015
#define PLP_DMA_BLE_BIT 0x00000016
#define PLP_DMA_2D_TCDM_BIT 0x0000017


#define FC_DMA_EVENT 8
#define CL_DMA_EVENT 22

static inline int mchan_alloc(){
  return *(volatile int*) MCHAN_COMMAND_QUEUE;
}

static inline void mchan_transfer(unsigned int len, char type, char incr, char twd_ext, char twd_tcdm, char ele, char ile, char ble, unsigned int ext_addr, unsigned int tcdm_addr, unsigned int ext_count, unsigned int ext_stride, unsigned int tcdm_count, unsigned int tcdm_stride)
{
  *(volatile int*) MCHAN_COMMAND_QUEUE = len | (type<<PLP_DMA_TYPE_BIT) | ( incr<<PLP_DMA_INCR_BIT) | (twd_ext <<PLP_DMA_2D_BIT) | (ele<<PLP_DMA_ELE_BIT) | (ile <<PLP_DMA_ILE_BIT) | (ble <<PLP_DMA_BLE_BIT) | (twd_tcdm << PLP_DMA_2D_TCDM_BIT);
 *(volatile int*) MCHAN_COMMAND_QUEUE = tcdm_addr;
 *(volatile int*) MCHAN_COMMAND_QUEUE = ext_addr;
 
 if (twd_ext  == 1)
   {
     *(volatile int*) MCHAN_COMMAND_QUEUE = ext_count;
     *(volatile int*) MCHAN_COMMAND_QUEUE = ext_stride;
   }
 
 if (twd_tcdm == 1)
   { 
     *(volatile int*) MCHAN_COMMAND_QUEUE = tcdm_count; 
     *(volatile int*) MCHAN_COMMAND_QUEUE = tcdm_stride;
   }
 
}

static inline void mchan_barrier(int id) {
  while(((*(volatile int*)(MCHAN_STATUS_REGISTER)) >> id ) & 0x1 ) {
    eu_evt_maskWaitAndClr(1<<FC_DMA_EVENT);
 }
}

static inline void mchan_free(int id) {
  *(volatile int*) MCHAN_STATUS_REGISTER = 0x1 << id;
}

static inline int fc_mchan_alloc(){
  return *(volatile int*) PE_MCHAN_COMMAND_QUEUE;
}

static inline void fc_mchan_transfer(unsigned int len, char type, char incr, char twd_ext, char twd_tcdm, char ele, char ile, char ble, unsigned int ext_addr, unsigned int tcdm_addr, unsigned short int ext_count, unsigned short int ext_stride, unsigned short int tcdm_count, unsigned short int tcdm_stride)
{
 *(volatile int*) PE_MCHAN_COMMAND_QUEUE = len | (type<<PLP_DMA_TYPE_BIT) | ( incr<<PLP_DMA_INCR_BIT) | (twd_ext <<PLP_DMA_2D_BIT) | (ele<<PLP_DMA_ELE_BIT) | (ile <<PLP_DMA_ILE_BIT) | (ble <<PLP_DMA_BLE_BIT)| (twd_tcdm << PLP_DMA_2D_TCDM_BIT);
 *(volatile int*) PE_MCHAN_COMMAND_QUEUE = tcdm_addr;
 *(volatile int*) PE_MCHAN_COMMAND_QUEUE = ext_addr;
 
 if (twd_ext  == 1)
   {
     *(volatile int*) MCHAN_COMMAND_QUEUE = ext_count;
     *(volatile int*) MCHAN_COMMAND_QUEUE = ext_stride;
   }
 
 if (twd_tcdm == 1)
   { 
     *(volatile int*) MCHAN_COMMAND_QUEUE = tcdm_count; 
     *(volatile int*) MCHAN_COMMAND_QUEUE = tcdm_stride;
   }
 
}

static inline void fc_mchan_barrier(int id) {
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

static inline void fc_mchan_free(int id) {
  *(volatile int*) PE_MCHAN_STATUS_REGISTER = 0x1 << id;
}

#endif
