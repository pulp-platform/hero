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

#ifndef __OMP_HAL_H__
#define __OMP_HAL_H__

#include <stdint.h>

/* HEADERS */
#include "config.h"

#ifndef ALWAYS_INLINE
#define ALWAYS_INLINE static inline __attribute__ ((always_inline))
#endif

#ifndef NULL
#define NULL ((void *) 0x0) /* Standard C */
#endif


#include "appsupport.h"
#include "omp-bar.h"
#include "memutils.h"
#include "omp-lock.h"
#include "mutex.h"

#define gomp_assert(x) \
{\
    if( ! (x)) {\
        printf("[%d][%d][GOMP] Assert failed at file %s line %d\n", (int) get_cl_id(), (int) get_proc_id(), __FILE__, __LINE__); \
        abort();\
    }\
}

ALWAYS_INLINE void
perfInitAndStart()
{
#ifdef PROFILE0
    cpu_perf_conf_events(PCER_ALL_EVENTS_MASK);
    cpu_perf_setall(0);
    cpu_perf_conf(PCMR_ACTIVE | PCMR_SATURATE);
#endif
}

ALWAYS_INLINE void
gomp_hal_init()
{
    // In case one cluster above the maximum number supported enters here,just make it sleep forerever
    if (get_cl_id() >= DEFAULT_MAXCL) {
        while (1) eu_evt_maskWaitAndClr(0);
    }

    gomp_assert(get_num_procs() <= DEFAULT_MAX_PE);

    /* Set Event Line to 1 */
#if EU_VERSION == 1
    set_evnt_mask_low( get_proc_id(), 1 ); //configure the event mask
#else
    eu_evt_maskSet( 1<<0 );
#endif

    /* Start Performance Counters */
    perfInitAndStart();
}    



#endif /* __HAL_H__ */
