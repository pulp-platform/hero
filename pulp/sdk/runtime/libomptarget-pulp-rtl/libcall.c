//===------------ libcall.cu - NVPTX OpenMP user calls ----------- CUDA -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is dual licensed under the MIT and the University of Illinois Open
// Source Licenses. See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the OpenMP runtime functions that can be
// invoked by the user in an OpenMP region
//
//===----------------------------------------------------------------------===//

#include "omptarget-pulp.h"
#include "pulp.h"

// Timer precision is 1ns
#define TIMER_PRECISION ((double)1E-9)

#ifndef DEBUG
#define DEBUG
#endif

#ifdef DEBUG
#define DP(...) printf("---> " __VA_ARGS__ "\n")
#else
#define DP(...)
#endif

EXTERN double omp_get_wtick(void) {
  DP("omp_get_wtick");
  return TIMER_PRECISION;
}

EXTERN double omp_get_wtime(void) {
  DP("omp_get_wtime");
  return 0.0;
}

EXTERN void omp_set_num_threads(int num) {
  DP("omp_set_num_threads");
  omp_t *omp = omp_getData();
  omp->numThreads = num;
  if(omp->numThreads > omp->maxThreads) {
    omp->numThreads = omp->maxThreads;
  }
}

EXTERN int omp_get_max_threads(void) {
  DP("omp_get_max_threads");
  omp_t *omp = omp_getData();
  return omp->numThreads;
}

EXTERN int omp_get_thread_limit(void) {
  DP("omp_get_thread_limit");
  omp_t *omp = omp_getData();
  return omp->maxThreads;
}

EXTERN int omp_get_num_procs(void) {
  DP("omp_get_num_procs");
  return 1;
}

EXTERN int omp_in_parallel(void) {
  DP("omp_in_parallel");
  return 0;
}

EXTERN int omp_in_final(void) {
  DP("omp_in_final");
  return 1;
}

EXTERN void omp_set_dynamic(int flag) {
  DP("omp_set_dynamic");
}

EXTERN int omp_get_dynamic(void) {
  DP("omp_get_dynamic");
  return 0;
}

EXTERN void omp_set_nested(int flag) {
  DP("omp_set_nested");
}

EXTERN int omp_get_nested(void) {
  DP("omp_get_nested");
  return 0;
}

EXTERN void omp_set_max_active_levels(int level) {
  DP("omp_set_max_active_levels");
}

EXTERN int omp_get_max_active_levels(void) {
  DP("omp_get_max_active_levels");
  return 1;
}

EXTERN int omp_get_level(void) {
  DP("omp_get_level");
  return 0;
}

EXTERN int omp_get_active_level(void) {
  DP("omp_get_active_level");
  return 0;
}

EXTERN int omp_get_ancestor_thread_num(int level) {
  DP("omp_get_ancestor_thread_num");
  return 0;
}

EXTERN int omp_get_team_size(int level) {
  DP("omp_get_team_size");
  return 1;
}

EXTERN void omp_get_schedule(omp_sched_t *kind, int *modifier) {
  DP("omp_get_schedule");
}

EXTERN void omp_set_schedule(omp_sched_t kind, int modifier) {
  DP("omp_set_schedule");
}

EXTERN omp_proc_bind_t omp_get_proc_bind(void) {
  DP("omp_proc_bind_t");
  return true;
}

EXTERN int omp_get_num_places(void) {
  DP("omp_get_num_places");
  return 0;
}

EXTERN int omp_get_place_num_procs(int place_num) {
  DP("omp_get_place_num_procs");
  return 0;
}

EXTERN void omp_get_place_proc_ids(int place_num, int *ids) {
  DP("omp_get_place_proc_ids");
}

EXTERN int omp_get_place_num(void) {
  DP("omp_get_place_num");
  return 0;
}

EXTERN int omp_get_partition_num_places(void) {
  DP("omp_get_partition_num_places");
  return 0;
}

EXTERN void omp_get_partition_place_nums(int *place_nums) {
  DP("omp_get_partition_place_nums");
}

EXTERN int omp_get_cancellation(void) {
  DP("omp_get_cancellation");
  return false;
}

EXTERN void omp_set_default_device(int deviceId) {
  DP("omp_set_default_device");
}

EXTERN int omp_get_default_device(void) {
  DP("omp_get_default_device");
  return 0;
}

EXTERN int omp_get_num_devices(void) {
  DP("omp_get_num_devices");
  return 0;
}

EXTERN int omp_get_num_teams(void) {
  DP("omp_get_num_teams");
  return 1;
}

EXTERN int omp_get_team_num() {
  DP("omp_get_team_num");
  return 0;
}

EXTERN int omp_is_initial_device(void) {
  DP("omp_is_initial_device");
  return 0;
}

// Unspecified on the device.
EXTERN int omp_get_initial_device(void) {
  DP("omp_get_initial_device");
  return 0;
}

// Unused for now.
EXTERN int omp_get_max_task_priority(void) {
  DP("omp_get_max_task_priority");
  return 0;
}

////////////////////////////////////////////////////////////////////////////////
// locks
////////////////////////////////////////////////////////////////////////////////

EXTERN void omp_init_lock(omp_lock_t *lock) {
}

EXTERN void omp_destroy_lock(omp_lock_t *lock) {
}

EXTERN void omp_set_lock(omp_lock_t *lock) {
}

EXTERN void omp_unset_lock(omp_lock_t *lock) {
}

EXTERN int omp_test_lock(omp_lock_t *lock) {
  return 0;
}

// for xlf Fotran
// Fotran, the return is LOGICAL type

#define FLOGICAL long
EXTERN FLOGICAL __xlf_omp_is_initial_device_i8() {
  int ret = omp_is_initial_device();
  if (ret == 0)
    return (FLOGICAL)0;
  else
    return (FLOGICAL)1;
}

EXTERN int __xlf_omp_is_initial_device_i4() {
  int ret = omp_is_initial_device();
  if (ret == 0)
    return 0;
  else
    return 1;
}

EXTERN long __xlf_omp_get_team_num_i4() {
  int ret = omp_get_team_num();
  return (long)ret;
}

EXTERN long __xlf_omp_get_num_teams_i4() {
  int ret = omp_get_num_teams();
  return (long)ret;
}

