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

#ifndef __MEMUTILS_H__
#define __MEMUTILS_H__

#include <stdint.h>
#include <rt/rt_alloc.h>

static inline void * l1malloc(size_t size){
  void * ptr = rt_alloc(RT_ALLOC_CL_DATA, size + 0x4U);
  if ((uint32_t) ptr == 0x0)
    return (void *) 0x0;
  *(uint32_t *)(ptr) = size + 0x4U;
  return (void *) ((uint32_t *)ptr++);
}

static inline void l1free(void *ptr){
  uint32_t size = *((uint32_t *)ptr--);
  rt_free(RT_ALLOC_CL_DATA, (void *)((uint32_t *)ptr--), size);
}

static inline void * l2malloc(size_t size){
  void * ptr = rt_alloc(RT_ALLOC_L2_CL_DATA, size + 0x4U);
  if ((uint32_t) ptr == 0x0)
    return (void *) 0x0;
  *(uint32_t *)(ptr) = size + 0x4U;
  return (void *) ((uint32_t *)ptr++);
}

static inline void l2free(void *ptr){
  uint32_t size = *((uint32_t *)ptr--);
  rt_free(RT_ALLOC_L2_CL_DATA, (void *)((uint32_t *)ptr--), size);
}

static inline void * shmalloc(uint32_t size){
  return l1malloc(size); 
}

static inline void shfree(void *address){
  l1free(address);
}

#endif
