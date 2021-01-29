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

#include "omp-lock.h"

/*********************************** standard APIs ***********************************************/

void omp_set_lock(omp_lock_t *lock) {
    gomp_hal_lock(lock);
}

void omp_unset_lock(omp_lock_t *lock) {
    gomp_hal_unlock(lock);
}

void omp_init_lock(omp_lock_t *lock) {
    gomp_hal_init_lock(lock);
}

int omp_test_lock(omp_lock_t *lock) {
    return gomp_hal_test_lock(lock);
}

void omp_destroy_lock(omp_lock_t *lock) {
    gomp_hal_destroy_lock(lock);
}
