/*
 * Copyright (C) 2018 ETH Zurich and University of Bologna
 * 
 * Authors: 
 *    Alessandro Capotondi, UNIBO, (alessandro.capotondi@unibo.it)
 */

/* Copyright (C) 2005-2014 Free Software Foundation, Inc.
 * C ontributed by Richard Henderson <r*th@redhat.com>.
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

/* This file handles the TARGET construct.  */

#include "libgomp.h"
#include "hal/pulp.h" // pulp_tryread_prefetch()

// #define OMP_TARGET_DEBUG

#if PULP_CHIP == CHIP_HERO_Z_7045
void
GOMP_target (int device, void (*fn) (void *), const void *unused,
       size_t mapnum, void **hostaddrs, size_t *sizes,
       unsigned char *kinds)
{
  target_desc.fn = fn;
  target_desc.hostaddrs = hostaddrs;
  target_desc.nteams = 0x1U;
  target_desc.threadLimit = DEFAULT_TARGET_THREAD_LIMIT;

#ifdef OMP_TARGET_DEBUG  
  printf("[%d][%d][GOMP_target] fn 0x%x, data 0x%x, nteams %d, threadLimit %d\n", get_cl_id(), get_proc_id(), target_desc.fn, target_desc.hostaddrs, target_desc.nteams, target_desc.threadLimit);
#endif

  fn(hostaddrs);

#ifdef OMP_TARGET_DEBUG  
  printf("[%d][%d][GOMP_target] calling MSGBarrier_swDocking_Wait....\n", get_cl_id(), get_proc_id());
#endif
  MSGBarrier_swDocking_Wait(target_desc.nteams);
}

void
GOMP_teams (unsigned int num_teams, unsigned int thread_limit)
{
  if(get_cl_id() == MASTER_ID)
  {
    target_desc.nteams = num_teams > DEFAULT_TARGET_MAX_NTEAMS || num_teams == 0 ? DEFAULT_TARGET_MAX_NTEAMS : num_teams;
    target_desc.threadLimit = thread_limit > DEFAULT_TARGET_THREAD_LIMIT || thread_limit == 0 ? DEFAULT_TARGET_THREAD_LIMIT : thread_limit;

    for(uint32_t i = 1; i < target_desc.nteams; ++i)
      gomp_hal_hwTrigg_Team( i );
  }
  gomp_set_thread_pool_idle_cores( target_desc.threadLimit - 1);

  #ifdef OMP_TARGET_DEBUG  
  printf("[%d][%d][GOMP_teams] fn 0x%x, data 0x%x, nteams %d, threadLimit %d\n", get_cl_id(), get_proc_id(), target_desc.fn, target_desc.hostaddrs, target_desc.nteams, target_desc.threadLimit);
  #endif
}

int
omp_get_team_num(void)
{
  return get_cl_id();
}

int
omp_get_num_teams(void)
{
  return target_desc.nteams;
}

#else // PULP_CHIP == CHIP_HERO_Z_7045

/**
 * GOMP target wrapper for GCC 7.x.
 */
void
GOMP_target_ext (int device, void (*fn) (void *), size_t mapnum,
                 void **hostaddrs, size_t *sizes, unsigned short *kinds,
                 unsigned int flags, void **depend, void **args)
{
  GOMP_target(device, fn, NULL, mapnum, hostaddrs, sizes, kinds);
}

/**
 * GOMP "fake" target for bigPULP standalone mode. This "fake" target just ensures that the
 * compiler extension inserting TRYX calls is triggered.
 */
void
GOMP_target (int dev, void (*fn)(void *), void *dev_fn, unsigned int num_args,
             void *omp_data_arr, void *omp_data_sizes, void *omp_data_kinds)
{
  int * data;
  unsigned int i;
  int size = 0;

  for (i=0; i<num_args; i++) {
    size += ((int *) omp_data_sizes)[i];
  }

  data = (int *)l1malloc(size);

  for (i=0; i<num_args; i++) {
    int *node = (int *)((int *) omp_data_arr)[i];
    data[i] = (int)node;
  }

  // Just execute the TARGET function from the caller
  fn (data);

  l1free(data);

  return;
}

#endif // PULP_CHIP == CHIP_HERO_Z_7045

int
GOMP_pulp_RAB_tryread(unsigned int * addr)
{
  return pulp_tryread_prefetch(addr);
}

void
GOMP_pulp_RAB_trywrite(unsigned int * addr, unsigned int value)
{
  pulp_trywrite(addr, value);

  return;
}
