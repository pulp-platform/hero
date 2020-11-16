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
#include <stdbool.h>
#include <stdio.h>
#include "omp.h"
#include "interface.h"
#include <stdint.h>
#include <string.h> // memcmp

typedef kmp_uint64 _kmp_ptr64;
typedef kmp_uint32 _kmp_ptr32;

typedef void (*__task_type32)(_kmp_ptr32, _kmp_ptr32, _kmp_ptr32);
typedef void (*__task_type64)(_kmp_ptr64, _kmp_ptr64, _kmp_ptr64);
static void __microtask_wrapper(void *arg)
{
  kmp_int32 id = omp_get_thread_num();
  _kmp_ptr32 *args = (_kmp_ptr32*) arg;
  __task_type32 fn = (__task_type32) args[0];
  _kmp_ptr32 id_addr = (_kmp_ptr32)((uint32_t) &id);
  _kmp_ptr32 arg_addr = (_kmp_ptr32)(uint32_t) &args[1];
  fn(id_addr, id_addr, arg_addr);
}

void __kmpc_fork_call(ident_t *loc, kmp_int32 argc, kmpc_micro microtask, ...)
{
  omp_t *_this = omp_getData();

  va_list ap;
  int arg_size = 0;
  arg_size = (argc+1)*sizeof(_kmp_ptr32);
  void *args = rt_alloc(RT_ALLOC_FC_DATA, arg_size);
  ((_kmp_ptr32*)args)[0] = (_kmp_ptr32) microtask;
  va_start(ap, microtask);
  for(int i=1; i<=argc; ++i) {
    ((_kmp_ptr32*)args)[i] = (_kmp_ptr32) va_arg(ap, _kmp_ptr32);
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
  if(omp->numThreads > omp->maxThreads) {
    omp->numThreads = omp->maxThreads;
  }
}

kmp_int32
__kmpc_global_thread_num(ident_t *loc)
{
  return omp_get_thread_num();
}

void
__kmpc_for_static_init_4( ident_t *loc, kmp_int32 gtid, enum sched_type sched, kmp_int32 *plastiter,
                          kmp_int32 *plower, kmp_int32 *pupper,
                          kmp_int32 *pstride, kmp_int32 incr, kmp_int32 chunk )
{
  omp_t *omp = omp_getData();
  omp_team_t *team = getTeam(omp);
  int threadNum = getThreadNum(omp);
  int loopSize = (*pupper - *plower) / incr + 1;
  int globalUpper = *pupper;

  // chunk size is specified
  if(sched == 33){
    int span = incr * chunk;
    *pstride = span * team->nbThreads;
    *plower = *plower + span * threadNum;
    *pupper = *plower + span - incr;
    int beginLastChunk = globalUpper - (globalUpper % span);
    *plastiter = ((beginLastChunk - *plower) % *pstride) == 0;
  }

  // no specified chunk size
  else if(sched == 34){
    chunk = loopSize / team->nbThreads;
    int leftOver = loopSize - chunk * team->nbThreads;

    // calculate precise chunk size and lower and upper bound
    if(threadNum < leftOver){
      chunk++;
      *plower = *plower + threadNum * chunk * incr;
    }
    else *plower = *plower + threadNum * chunk * incr + leftOver;
    *pupper = *plower + chunk * incr - incr;

    if(plastiter != NULL) *plastiter = (*pupper == globalUpper && *plower <= globalUpper);
    *pstride = loopSize;
  }
}

void __kmpc_for_static_init_4u(ident_t *loc, kmp_int32 global_tid,
                               enum sched_type sched, kmp_int32 *plastiter,
                               kmp_uint32 *plower, kmp_uint32 *pupper,
                               kmp_int32 *pstride, kmp_int32 incr,
                               kmp_int32 chunk) {
  kmp_int32 ilower = *plower;
  kmp_int32 iupper = *pupper;
  __kmpc_for_static_init_4(loc, global_tid, sched, plastiter, &ilower, &iupper, pstride, incr, chunk);
  *plower = ilower;
  *pupper = iupper;
}
void __kmpc_for_static_init_8(ident_t *loc, kmp_int32 global_tid,
                              enum sched_type sched, kmp_int32 *plastiter,
                              kmp_int64 *plower, kmp_int64 *pupper,
                              kmp_int64 *pstride, kmp_int64 incr,
                              kmp_int64 chunk) {
  kmp_int32 ilower = *plower;
  kmp_int32 iupper = *pupper;
  kmp_int32 istride = *pstride;
  __kmpc_for_static_init_4(loc, global_tid, sched, plastiter, &ilower, &iupper, &istride, incr, chunk);
  *plower = ilower;
  *pupper = iupper;
  *pstride = istride;

  omp_t *omp = omp_getData();
}
void __kmpc_for_static_init_8u(ident_t *loc, kmp_int32 global_tid,
                               enum sched_type sched, kmp_int32 *plastiter,
                               kmp_uint64 *plower, kmp_uint64 *pupper,
                               kmp_int64 *pstride, kmp_int64 incr,
                               kmp_int64 chunk) {
  kmp_int32 ilower = *plower;
  kmp_int32 iupper = *pupper;
  kmp_int32 istride = *pstride;
  __kmpc_for_static_init_4(loc, global_tid, sched, plastiter, &ilower, &iupper, &istride, incr, chunk);
  *plower = ilower;
  *pupper = iupper;
  *pstride = istride;
}


void
__kmpc_for_static_fini( ident_t *loc, kmp_int32 global_tid )
{
  omp_t *_this = omp_getData();
  doBarrier(getTeam(_this));
}

void __kmpc_barrier(ident_t *loc_ref, kmp_int32 tid) {
  omp_t *_this = omp_getData();
  doBarrier(getTeam(_this));
}

kmp_int32
__kmpc_cancel_barrier(ident_t *loc, kmp_int32 gtid) {
  __kmpc_barrier(loc, gtid);
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

void
__kmpc_dispatch_init_4( ident_t *loc, kmp_int32 gtid, enum sched_type schedule,
                        kmp_int32 lb, kmp_int32 ub, kmp_int32 st, kmp_int32 chunk )
{
  omp_team_t *team = getCurrentTeam();
  dynLoopInitNoIter(team, lb, ub, st, chunk);
}

int
__kmpc_dispatch_next_4( ident_t *loc, kmp_int32 gtid, kmp_int32 *p_last,
                        kmp_int32 *p_lb, kmp_int32 *p_ub, kmp_int32 *p_st )
{
  omp_team_t *team = getCurrentTeam();

  // The stride is actually always 1
  *p_st = 1;
  int result = dynLoopIter(team, (int*) p_lb, (int*) p_ub, (int*) p_last);
  return result;
}

void
__kmpc_dispatch_init_8u( ident_t *loc, kmp_int32 gtid, enum sched_type schedule,
                         kmp_uint64 lb, kmp_uint64 ub, kmp_int64 st, kmp_int64 chunk )
{
  kmp_int32 lower = lb;
  kmp_int32 upper = ub;
  kmp_int32 stride = st;
  kmp_int32 chunk_size = chunk;
  __kmpc_dispatch_init_4(loc, gtid, schedule, lower, upper, stride, chunk_size);
}

int
__kmpc_dispatch_next_8u( ident_t *loc, kmp_int32 gtid, kmp_int32 *p_last,
                        kmp_uint64 *p_lb, kmp_uint64 *p_ub, kmp_int64 *p_st )
{
  kmp_int32 lower = *p_lb;
  kmp_int32 upper = *p_ub;
  kmp_int32 stride = *p_st;
  int result = __kmpc_dispatch_next_4(loc, gtid, p_last, &lower, &upper, &stride);
  *p_lb = lower;
  *p_ub = upper;
  *p_st = stride;
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


//reduction

/*
 * loc: source location information
 * global_tid: global thread number
 * num_vars: number of items(variables) to be reduced
 * reduce_size: size of data in bytes to be reduced
 * reduce_data: pointer to data to be reduced
 * reduce_func: callback function providing reduction
 *operation on two operands and returning result of reduction in lhs_data
 * lck: pointer to the unique lock data structure
 */
kmp_int32 __kmpc_reduce(ident_t *loc, kmp_int32 global_tid, \
  kmp_int32 num_vars, size_t reduce_size, void * reduce_data, \
  void (*reduce_func)(void *lhs_data, void *rhs_data), kmp_critical_name *lck)
{
  return __kmpc_reduce_nowait(loc, global_tid, num_vars, reduce_size, reduce_data, reduce_func, lck);
}

kmp_int32 __kmpc_reduce_nowait(ident_t *loc, kmp_int32 global_tid, \
  kmp_int32 num_vars, size_t reduce_size, void * reduce_data, \
  void (*reduce_func)(void *lhs_data, void *rhs_data), kmp_critical_name *lck)
{
  // use of (emulated) atomics requires two to be returned for all threads (including master)
  // TODO: implement other reduction methods (returning 1 for master and 0 for other threads)
  return 2;
}

void __kmpc_end_reduce(ident_t *loc, kmp_int32 global_tid, kmp_critical_name *lck){}

void __kmpc_end_reduce_nowait(ident_t *loc, kmp_int32 global_tid, kmp_critical_name *lck){}


static inline void __mem_fence()
{
  __asm__ __volatile__ ("" : : : "memory");
}
static inline uint32_t load_reserved(const volatile void* const address)
{
  __mem_fence();
  uint32_t value;
  __asm__ volatile(
          "lr.w %[value], (%[address])"
          : [value] "=r" (value)
          : [address] "r" (address)
      );
  __mem_fence();
  return value;
}

// Returns true if successful, false if not.
static inline bool store_conditional(volatile void* const address, const uint32_t value)
{
  __mem_fence();
  bool fail;
  __asm__ volatile(
          "sc.w %[fail], %[value], (%[address])"
          : [fail] "=r" (fail)
          : [value] "r" (value), [address] "r" (address)
      );
  __mem_fence();
  return !fail;
}

typedef bool mutex_t; // true = locked

// Lock a mutex and return its prior state.
static inline mutex_t mutex_trylock(mutex_t* const mutex)
{
  __mem_fence();
  mutex_t res = true;
  __asm__ volatile(
          "amoor.w %[res], %[res], (%[mutex])"
          : [res] "+r" (res)
          : [mutex] "r" (mutex)
      );
  __mem_fence();
  return res;
}

// Lock a mutex by retrying until the lock was obtained.
static void mutex_lock(mutex_t* const mutex)
{
  while (mutex_trylock(mutex)) { }
}

// Unlock a mutex.  Only call this function while holding the mutex.
static inline void mutex_unlock(mutex_t* const mutex)
{
  __mem_fence();
  *mutex = false;
  __mem_fence();
}

mutex_t __atomic_cex_mutex;
bool atomic_compare_exchange(const size_t size, void* const ptr, void* const expected,
    const void* const desired, const int success_order, const int failure_order, void* prev)
{
  const uint32_t addr = (uint32_t)ptr;
  // For operations on 32-bit words in L2 that are 32-bit-aligned, use LR and SC.
  if (size == 4 && (addr & 0xFF000000) == 0x1C000000 && (addr & 0x3) == 0) {
    // Compare the contents of `*ptr` with the contents of `*expected`.
    const uint32_t tmp = load_reserved(ptr);
    if(prev) (*(int*)prev) = tmp;
    if (tmp == *(uint32_t*)expected) {
      // If equal, use SC to write `desired` into `ptr` and return whether the write happened.
      return store_conditional(ptr, *(uint32_t*)desired);
    } else {
      // If not equal, write the current contents of `*ptr` into `*expected` and return false.
      *(uint32_t*)expected = tmp;
      return false;
    }
  // For all other sizes and address regions, use a mutex.
  } else {
    mutex_lock(&__atomic_cex_mutex);
    bool modified;
    // Compare the contents of `*ptr` with the contents of `*expected`.
    if(prev) memcpy(prev, ptr, size);
    if (memcmp(ptr, expected, size) == 0) {
      // If equal, write `desired` into `ptr` and return true.
      memcpy(ptr, desired, size);
      modified = true;
    } else {
      // If not equal, write the current contents of `*ptr` into `*expected` and return false.
      memcpy(expected, ptr, size);
      modified = false;
    }
    mutex_unlock(&__atomic_cex_mutex);
    return modified;
  }
}

char __sync_val_compare_and_swap_1(char* ptr, char expected, char desired) {
    char prev;
    atomic_compare_exchange(1, ptr, &expected, &desired, 0, 0, &prev);
    return prev;
}
short __sync_val_compare_and_swap_2(short* ptr, short expected, short desired) {
    short prev;
    atomic_compare_exchange(2, ptr, &expected, &desired, 0, 0, &prev);
    return prev;
}
int __sync_val_compare_and_swap_4(int* ptr, int expected, int desired) {
    int prev;
    atomic_compare_exchange(4, ptr, &expected, &desired, 0, 0, &prev);
    return prev;
}
long long __sync_val_compare_and_swap_8(long long* ptr, long long expected, long long desired) {
    long prev;
    atomic_compare_exchange(8, ptr, &expected, &desired, 0, 0, &prev);
    return prev;
}

bool __atomic_compare_exchange(const size_t size, void* const ptr, void* const expected,
    const void* const desired, const int success_order, const int failure_order) {
  return atomic_compare_exchange(size, ptr, expected, desired, success_order, failure_order, NULL);
}

mutex_t __atomic_load_mutex;
void __atomic_load(const size_t size, const void* const ptr, void* const ret,
    const int ordering)
{
  const uint32_t addr = (uint32_t)ptr;
  // For byte, halfword, and word loads that are aligned, just use regular pointer dereferences.
  if (size == 4 && (addr & 0x3) == 0) {
    *(uint32_t*)ret = *(uint32_t*)ptr;
  } else if (size == 2 && (addr & 0x1) == 0) {
    *(uint16_t*)ret = *(uint16_t*)ptr;
  } else if (size == 1) {
    *(uint8_t*)ret = *(uint8_t*)ptr;
  } else {
    // For everything else, use a mutex and `memcpy`.
    mutex_lock(&__atomic_load_mutex);
    memcpy(ret, ptr, size);
    mutex_unlock(&__atomic_load_mutex);
  }
}

kmp_int32 __kmpc_master(ident_t *loc, kmp_int32 global_tid)
{
  if(omp_get_thread_num() == 0) return 1;
  else return 0;
}
void __kmpc_end_master(ident_t *loc, kmp_int32 global_tid) {}

void __kmpc_flush(ident_t *loc) {}
