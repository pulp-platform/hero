/*
 * Copyright (C) 2018 ETH Zurich and University of Bologna
 * 
 * Authors: 
 *    Alessandro Capotondi, UNIBO, (alessandro.capotondi@unibo.it)
 *    Germain Haugou,       ETH,   (germain.haugou@iis.ee.ethz.ch)
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

#ifndef __OMP_LOCK_H__
#define __OMP_LOCK_H__

#include "appsupport.h"
#include "memutils.h"

typedef uint32_t omp_lock_t;

// #define OMP_LOCK_DEBUG

#define BUSY_LOCK   0xffffffffU
#define FREE_LOCK   0x0U

/* gomp_hal_lock() - block until able to acquire lock "lock" */
static inline void
gomp_hal_lock( omp_lock_t *lock )
{
	volatile omp_lock_t *lock_ptr = (volatile omp_lock_t *)( (uint32_t) lock + (1<<ARCHI_L1_TAS_BIT));

#ifdef OMP_LOCK_DEBUG
    printf("[%d-%d][gomp_hal_lock] Locking at 0x%x (0x%x, 0x%x) \n", get_proc_id(), get_cl_id(), lock_ptr, lock,  (1<<ARCHI_L1_TAS_BIT));
#endif

    while (*lock_ptr == BUSY_LOCK);

#ifdef OMP_LOCK_DEBUG    
    printf("[%d-%d][gomp_hal_lock] Locked  at 0x%x\n", get_proc_id(), get_cl_id(), lock_ptr);
#endif
}

/* gomp_hal_unlock() - release lock "lock" */
static inline void
gomp_hal_unlock( omp_lock_t *lock )
{
    *lock = FREE_LOCK;
}

static inline void
gomp_hal_init_lock( omp_lock_t *lock )
{    
    lock = (omp_lock_t *)l1malloc(sizeof(omp_lock_t));
    *lock = 0x0U;
}

static inline int
gomp_hal_test_lock( omp_lock_t *lock )
{
    int ret = (int ) *lock;
    *lock = FREE_LOCK;
    return ret;
}

static inline void
gomp_hal_destroy_lock( omp_lock_t *lock )
{
    l1free(lock);
}

/*********************************** standard APIs ***********************************************/

void omp_set_lock(omp_lock_t *);
void omp_unset_lock(omp_lock_t *);
void omp_init_lock(omp_lock_t *);
int omp_test_lock(omp_lock_t *);
void omp_destroy_lock(omp_lock_t *);

#endif