/*
 * Copyright (C) 2018 ETH Zurich and University of Bologna
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

/*
 * Authors: Germain Haugou, ETH (germain.haugou@iis.ee.ethz.ch)
 */

#include "omp.h"
#include "ompRt.h"

/*
 * LLVM wrapper
 */

typedef void (*__task_type)(void*);
static void __microtask_wrapper(void *arg) 
{
   void **args = (void**) arg;
   __task_type fn = (__task_type) args[0];
   int id = omp_get_thread_num();
   args[0] = args[1] = (void*) &id;

   fn((void*)args);
}

void __kmpc_fork_call(ident_t *loc, kmp_int32 argc, kmpc_micro microtask, ...)
{
  omp_t *_this = omp_getData();

  va_list ap;
  int arg_size = (2+argc)*sizeof(void*);
  void **args = (void**) rt_alloc(RT_ALLOC_FC_DATA, arg_size);
  args[0] = (void*) microtask;
  args[1] = (void*) -1;
  va_start(ap, microtask);
  for(int i=0; i<argc; ++i) {
      args[i+2] = va_arg( ap, int*);
  }
  va_end(ap);

  parallelRegion(args, __microtask_wrapper, _this->numThreads);

  rt_free(RT_ALLOC_FC_DATA, args, arg_size); 
}

void
__kmpc_push_num_threads(ident_t *loc, kmp_int32 global_tid, kmp_int32 num_threads )
{
  omp_t *omp = omp_getData();
  omp->numThreads = num_threads;
}

kmp_int32
__kmpc_global_thread_num(ident_t *loc)
{
  return omp_get_thread_num();
}

void
__kmpc_for_static_init_4( ident_t *loc, kmp_int32 gtid, kmp_int32 schedtype, kmp_int32 *plastiter,
                      kmp_int32 *plower, kmp_int32 *pupper,
                      kmp_int32 *pstride, kmp_int32 incr, kmp_int32 chunk )
{
  printf("HERE\n");
  omp_t *omp = omp_getData();
  omp_team_t *team = getTeam(omp);
  int threadNum = getThreadNum(omp);

  chunk = (*pupper - *plower + 1) / team->nbThreads;
  int span = incr * chunk;

  *pstride = span * team->nbThreads;
  *plower = *plower + span * threadNum;
  if(plastiter != NULL) *plastiter = *plower + span >= *pupper;
  *pupper = *plower + span - incr;
}

void
__kmpc_for_static_fini( ident_t *loc, kmp_int32 global_tid )
{
  omp_t *_this = omp_getData();
  doBarrier(getTeam(_this));
}

kmp_int32
__kmpc_cancel_barrier(ident_t *loc, kmp_int32 gtid) {
  omp_t *_this = omp_getData();
  userBarrier(getTeam(_this));
  return 0;
}

void __kmpc_critical( ident_t * loc, kmp_int32 global_tid, kmp_critical_name * crit )
{
  userCriticalStart(getCurrentTeam());
}

void __kmpc_end_critical(ident_t *loc, kmp_int32 global_tid, kmp_critical_name *crit)
{
  userCriticalEnd(getCurrentTeam());
}

enum sched_type {
  NONE
};

void
__kmpc_dispatch_init_4( ident_t *loc, kmp_int32 gtid, enum sched_type schedule,
                        kmp_int32 lb, kmp_int32 ub, kmp_int32 st, kmp_int32 chunk )
{
  omp_team_t *team = getCurrentTeam();
  dynLoopInitNoIter(team, lb, ub+1, st, chunk);
}

int
__kmpc_dispatch_next_4( ident_t *loc, kmp_int32 gtid, kmp_int32 *p_last,
                        kmp_int32 *p_lb, kmp_int32 *p_ub, kmp_int32 *p_st )
{
  omp_team_t *team = getCurrentTeam();

  // The stride is actually always 1
  *p_st = 1;
  int result = dynLoopIter(team, p_lb, p_ub, p_last);
  *p_ub = *p_ub - 1;
  return result;
}

kmp_int32
__kmpc_single(ident_t *loc, kmp_int32 global_tid)
{
  // Note that compared to gcc where there is no function called
  // at the end of the single program, we could implement
  // single pragma with a sinmple lock cleared in __kmpc_end_single, 
  // this makes us gain 15 cycles.
  return singleStart();
}

void
__kmpc_end_single(ident_t *loc, kmp_int32 global_tid)
{
}

typedef kmp_int32 (* kmp_routine_entry_t)( kmp_int32, void * );

typedef struct kmp_task {
    void *              shareds;            /**< pointer to block of pointers to shared vars   */
    kmp_routine_entry_t routine;            /**< pointer to routine to call for executing task */
    kmp_int32           part_id;            /**< part id for the task                          */
    kmp_routine_entry_t destructors;        /* pointer to function to invoke deconstructors of firstprivate C++ objects */
    /*  private vars  */
    size_t              size;
} kmp_task_t;

typedef int kmp_tasking_flags_t;
typedef int bool;

kmp_task_t *
__kmpc_omp_task_alloc( ident_t *loc_ref, kmp_int32 gtid, kmp_int32 flags,
                       size_t sizeof_kmp_task, size_t sizeof_shareds,
                       kmp_routine_entry_t task_entry )
{
  // TODO this is crashing if NULL is returned and libomp seems to ignore
  // memory exhaustion ...
  kmp_task_t *task = (kmp_task_t *)rt_alloc(RT_ALLOC_FC_DATA, sizeof(kmp_task_t) + sizeof_kmp_task + sizeof_shareds);
  task->routine = task_entry;
  task->part_id = 0;
  task->size = sizeof_kmp_task + sizeof_shareds; 
  return task;
}

kmp_int32
__kmpc_omp_task( ident_t *loc_ref, kmp_int32 gtid, kmp_task_t * new_task)
{
  new_task->routine(gtid, new_task);
  rt_free(RT_ALLOC_FC_DATA, (void*) new_task, sizeof(kmp_task_t) + new_task->size);
  return 0;
}
