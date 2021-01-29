/*
 * Copyright (C) 2018 ETH Zurich and University of Bologna
 * 
 * Authors: 
 *    Alessandro Capotondi, UNIBO, (alessandro.capotondi@unibo.it)
 */

/* Copyright (C) 2005-2014 Free Software Foundation, Inc.
 * 
 * This file is part of the GNU OpenMP Library (libgomp).
 * 
 * Libgomp is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3, or (at your option)
 * any later version.
 * 
 * Libgomp is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
 * more details.
 * 
 * Under Section 7 of GPL version 3, you are granted additional
 * permissions described in the GCC Runtime Library Exception, version
 * 3.1, as published by the Free Software Foundation.
 * 
 * You should have received a copy of the GNU General Public License and
 * a copy of the GCC Runtime Library Exception along with this program;
 * see the files COPYING3 and COPYING.RUNTIME respectively.  If not, see
 * <http://www.gnu.org/licenses/>.
 */


#ifndef __BAR_HW_H__
#define __BAR_HW_H__           

//#include "bar.h"
#if EU_VERSION == 1
#include "events.h"
#include "timer.h"
#include "events_ids.h"
#endif

/*** *** Low Level Event Unit APIs *** ***/
ALWAYS_INLINE void
gomp_hal_wait_hwBarrier_buff( uint32_t barrier_id )
{
#if EU_VERSION == 1    
    
    *(volatile int*) (WAIT_BARRIER) =  barrier_id;
    *(volatile int*) (CORE_CLKGATE) =  0x1;
    
    // Flush the pipeline
    #ifdef __riscv__
      asm volatile ("WFI");
    #else
    asm volatile ("l.psync");
    #endif
    
    *(volatile int*) (EV_BUFF_CLEAR) = 0x1;
#else
    eu_bar_trig_wait_clr(eu_bar_addr(barrier_id));
#endif
}

ALWAYS_INLINE void
gomp_hal_clear_hwBarrier_buff( )
{
#if EU_VERSION == 1    
    *(volatile int*) (EV_BUFF_CLEAR) = 0x1;
#else
    eu_bar_trig_wait_clr(eu_bar_addr(0));
#endif
}


ALWAYS_INLINE void
gomp_hal_set_hwBarrier( uint32_t barrier_id,
                        uint32_t nthreads,
                        uint32_t thMask )
{
#if EU_VERSION == 1
    *(volatile uint32_t*) (SET_BARRIER_BASE + 0x4U*barrier_id) = (nthreads << 16U) + thMask;
#else
    eu_bar_setup_mask(eu_bar_addr(barrier_id), thMask, thMask);
#endif
}

ALWAYS_INLINE void
gomp_hal_wait_hwEvent_buff( )
{
#if EU_VERSION == 1
    *(volatile int*) (CORE_CLKGATE) =  0x1;
    // Flush the pipeline
#ifdef __riscv__
  asm volatile ("WFI");
#else
  asm volatile ("l.psync");
#endif
    *(volatile int*) (EV_BUFF_CLEAR) = 0x1;
#else
    eu_evt_waitAndClr(1<<0);
#endif
}

/*** *** Master Slave Barrier APIs *** ***/

ALWAYS_INLINE void
MSGBarrier_hwWait( uint32_t barrier_id,
                   uint32_t nthreads,
                   uint32_t thMask)
{
#if EU_VERSION == 1
    gomp_hal_set_hwBarrier( barrier_id, nthreads, thMask);
#endif
    gomp_hal_wait_hwBarrier_buff( barrier_id );
}

ALWAYS_INLINE void
MSGBarrier_hwSlaveEnter( uint32_t barrier_id)
{
#if EU_VERSION == 1
    gomp_hal_wait_hwBarrier_buff( barrier_id );
#else
    if ((int32_t)barrier_id>0) gomp_hal_wait_hwBarrier_buff(barrier_id);
    gomp_hal_wait_hwEvent_buff( );
#endif
}

ALWAYS_INLINE void
MSGBarrier_hwRelease( uint32_t thMask )
{
    gomp_hal_hwTrigg_core( thMask );
}

ALWAYS_INLINE void
gomp_hal_hwBarrier( uint32_t barrier_id)
{
    gomp_hal_wait_hwBarrier_buff( barrier_id );
}

ALWAYS_INLINE void
MSGBarrier_hwDocking ( uint32_t pid )
{
    /* Notify the master I'm on the barrier */
    *(LNFLAGS(pid)) = 0x1U;
    
#ifdef OMP_BAR_DEBUG
    printf("[%d][%d][MSGBarrier_hwDocking] Arrived %d at 0x%x (%x)\n", get_proc_id(), get_cl_id(), pid, LNFLAGS( pid ), *(LNFLAGS( pid )));
#endif
    
    gomp_hal_wait_hwEvent_buff( );
}

#endif /*__BAR_HW_H__*/
