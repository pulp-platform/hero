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

#ifndef __OMP_BAR_H__
#define __OMP_BAR_H__

#include "omp-hal.h"

#if EU_VERSION == 1
#include "events.h"
#include "timer.h"
#include "events_ids.h"
#endif

// #define OMP_BAR_DEBUG

/* Software Barriers Data Type */
typedef volatile int32_t MSGBarrier;
#define Log2SizeofMSGBarrier (2U)

/* Software Barriers Base Address */
#define SWBAR_BASE_ADDR                     ( LIBGOMP_BASE )

/* Local Aliased Address */
#define SWBAR_LBASE_ADDR                    ( LIBGOMP_LBASE )

#define SWBAR_RFLAGS_SIZE                   (( DEFAULT_MAX_PE  << Log2SizeofMSGBarrier ))
#define SWBAR_NFLAGS_SIZE                   (( DEFAULT_MAXPROC << Log2SizeofMSGBarrier ))
#define SWBAR_SIZE                          ( SWBAR_RFLAGS_SIZE + SWBAR_NFLAGS_SIZE )
#define SWBAR_ID                            ( 0xFFFFFFFFU )

/* HW Wakeup Cores */
static inline void
gomp_hal_hwTrigg_core( uint32_t cmask )
{
#if EU_VERSION == 1
    *(volatile uint32_t*) ( TRIGG_BARRIER ) = cmask;
#ifdef OMP_BAR_DEBUG
        printf("[%d][%d][gomp_hal_hwTrigg_core] Trigger %x at 0x%x\n", get_proc_id(), get_cl_id(), cmask, get_hal_addr( get_cl_id(), OFFSET_EVENT0 ));
#endif
#else
	if (cmask) eu_evt_trig(eu_evt_trig_addr(0), cmask);
#endif
}

#include "bar-sw.h"
#include "bar-hw.h"

/* HW Wakeup Cores */
static inline void
gomp_hal_hwTrigg_Team( uint32_t cid )
{
#if EU_VERSION == 1
//     *(volatile uint32_t*) ( get_hal_addr( cid, OFFSET_EVENT0 )) = 0x1;
// #ifdef OMP_BAR_DEBUG
//         printf("[%d][%d][gomp_hal_hwTrigg_Team] Trigger %x ats 0x%x\n", get_proc_id(), get_cl_id(), 0x1, get_hal_addr( cid, OFFSET_EVENT0 ));
// #endif
	*NFLAGS( cid, 0x0U ) = 0x0U;
	volatile MSGBarrier *rflag = ((volatile MSGBarrier *) ( RFLAGS_BASE( cid )));
#ifdef OMP_BAR_DEBUG
	printf("[%d][%d][gomp_hal_hwTrigg_Team] Trigger %x at 0x%x\n", get_proc_id(), get_cl_id(), 0x1, rflag);
#endif	
    (*rflag)++;
#else
#endif
}

#endif /*__BAR_H__*/
