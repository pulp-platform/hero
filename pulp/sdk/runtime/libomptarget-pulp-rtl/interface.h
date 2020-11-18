//===------- interface.h - NVPTX OpenMP interface definitions ---- CUDA -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is dual licensed under the MIT and the University of Illinois Open
// Source Licenses. See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
//
// This file contains debug macros to be used in the application.
//
//  This file contains all the definitions that are relevant to
//  the interface. The first section contains the interface as
//  declared by OpenMP.  A second section includes library private calls
//  (mostly debug, temporary?) The third section includes the compiler
//  specific interfaces.
//
//===----------------------------------------------------------------------===//

#ifndef _INTERFACE_H_
#define _INTERFACE_H_

#include <stdlib.h>
#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>

#include "omptarget-pulp.h"

////////////////////////////////////////////////////////////////////////////////
// OpenMP interface
////////////////////////////////////////////////////////////////////////////////

typedef int32_t kmp_int32;
typedef uint32_t kmp_uint32;
typedef int64_t kmp_int64;
typedef uint64_t kmp_uint64;

typedef kmp_int32 kmp_critical_name[8];
typedef kmp_uint32 omp_lock_t;      /* arbitrary type of the right length */
typedef kmp_uint64 omp_nest_lock_t; /* arbitrary type of the right length */

typedef void (*kmpc_micro)              ( kmp_int32 * global_tid, kmp_int32 * bound_tid, ...);

typedef struct ident {
    kmp_int32 reserved_1;   /**<  might be used in Fortran; see above  */
    kmp_int32 flags;        /**<  also f.flags; KMP_IDENT_xxx flags; KMP_IDENT_KMPC identifies this union member  */
    kmp_int32 reserved_2;   /**<  not really used in Fortran any more; see above */
    kmp_int32 reserved_3;   /**< source[4] in Fortran, do not use for C++  */
    char const *psource;    /**< String describing the source location.
                               The string is composed of semi-colon separated fields which describe the source file,
                               the function and a pair of line numbers that delimit the construct.
                            */
} ident_t;

typedef enum omp_sched_t {
  omp_sched_static = 1,  /* chunkSize >0 */
  omp_sched_dynamic = 2, /* chunkSize >0 */
  omp_sched_guided = 3,  /* chunkSize >0 */
  omp_sched_auto = 4,    /* no chunkSize */
} omp_sched_t;

typedef enum sched_type {
  kmp_sch_lower = 32 , kmp_sch_static = 34 , kmp_sch_guided_chunked = 36 , kmp_sch_auto = 38 ,
  kmp_sch_static_steal = 44, kmp_sch_upper = 45, kmp_ord_lower = 64 , kmp_ord_static = 66 ,
  kmp_ord_auto = 70 , kmp_ord_upper = 72, kmp_distribute_static_chunked = 91, kmp_distribute_static = 92,
   kmp_nm_lower = 160 , kmp_nm_static = 162 , kmp_nm_guided_chunked = 164 , kmp_nm_auto = 166 ,
   kmp_nm_ord_static = 194 , kmp_nm_ord_auto = 198 , kmp_nm_upper = 200, kmp_sch_default = kmp_sch_static 
} sched_type;

typedef enum omp_proc_bind_t {
  omp_proc_bind_false = 0,
  omp_proc_bind_true = 1,
  omp_proc_bind_master = 2,
  omp_proc_bind_close = 3,
  omp_proc_bind_spread = 4
} omp_proc_bind_t;

EXTERN double omp_get_wtick(void);
EXTERN double omp_get_wtime(void);

EXTERN void omp_set_num_threads(int num);
EXTERN int omp_get_num_threads(void);
EXTERN int omp_get_max_threads(void);
EXTERN int omp_get_thread_limit(void);
EXTERN int omp_get_thread_num(void);
EXTERN int omp_get_num_procs(void);
EXTERN int omp_in_parallel(void);
EXTERN int omp_in_final(void);
EXTERN void omp_set_dynamic(int flag);
EXTERN int omp_get_dynamic(void);
EXTERN void omp_set_nested(int flag);
EXTERN int omp_get_nested(void);
EXTERN void omp_set_max_active_levels(int level);
EXTERN int omp_get_max_active_levels(void);
EXTERN int omp_get_level(void);
EXTERN int omp_get_active_level(void);
EXTERN int omp_get_ancestor_thread_num(int level);
EXTERN int omp_get_team_size(int level);

EXTERN void omp_init_lock(omp_lock_t *lock);
EXTERN void omp_init_nest_lock(omp_nest_lock_t *lock);
EXTERN void omp_destroy_lock(omp_lock_t *lock);
EXTERN void omp_destroy_nest_lock(omp_nest_lock_t *lock);
EXTERN void omp_set_lock(omp_lock_t *lock);
EXTERN void omp_set_nest_lock(omp_nest_lock_t *lock);
EXTERN void omp_unset_lock(omp_lock_t *lock);
EXTERN void omp_unset_nest_lock(omp_nest_lock_t *lock);
EXTERN int omp_test_lock(omp_lock_t *lock);
EXTERN int omp_test_nest_lock(omp_nest_lock_t *lock);

EXTERN void omp_get_schedule(omp_sched_t *kind, int *modifier);
EXTERN void omp_set_schedule(omp_sched_t kind, int modifier);
EXTERN omp_proc_bind_t omp_get_proc_bind(void);
EXTERN int omp_get_cancellation(void);
EXTERN void omp_set_default_device(int deviceId);
EXTERN int omp_get_default_device(void);
EXTERN int omp_get_num_devices(void);
EXTERN int omp_get_num_teams(void);
EXTERN int omp_get_team_num(void);
EXTERN int omp_is_initial_device(void);
EXTERN int omp_get_initial_device(void);
EXTERN int omp_get_max_task_priority(void);

////////////////////////////////////////////////////////////////////////////////
// OMPTARGET_NVPTX private (debug / temportary?) interface
////////////////////////////////////////////////////////////////////////////////

// for debug
EXTERN void __kmpc_print_str(char *title);
EXTERN void __kmpc_print_title_int(char *title, int data);
EXTERN void __kmpc_print_index(char *title, int i);
EXTERN void __kmpc_print_int(int data);
EXTERN void __kmpc_print_double(double data);
EXTERN void __kmpc_print_address_int64(kmp_int64 data);

////////////////////////////////////////////////////////////////////////////////
// file below is swiped from kmpc host interface
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// kmp specifc types
////////////////////////////////////////////////////////////////////////////////

typedef enum kmp_sched_t {
  kmp_sched_static_chunk = 33,
  kmp_sched_static_nochunk = 34,
  kmp_sched_dynamic = 35,
  kmp_sched_guided = 36,
  kmp_sched_runtime = 37,
  kmp_sched_auto = 38,

  kmp_sched_static_ordered = 65,
  kmp_sched_static_nochunk_ordered = 66,
  kmp_sched_dynamic_ordered = 67,
  kmp_sched_guided_ordered = 68,
  kmp_sched_runtime_ordered = 69,
  kmp_sched_auto_ordered = 70,

  kmp_sched_distr_static_chunk = 91,
  kmp_sched_distr_static_nochunk = 92,
  kmp_sched_distr_static_chunk_sched_static_chunkone = 93,

  kmp_sched_default = kmp_sched_static_nochunk,
  kmp_sched_unordered_first = kmp_sched_static_chunk,
  kmp_sched_unordered_last = kmp_sched_auto,
  kmp_sched_ordered_first = kmp_sched_static_ordered,
  kmp_sched_ordered_last = kmp_sched_auto_ordered,
  kmp_sched_distribute_first = kmp_sched_distr_static_chunk,
  kmp_sched_distribute_last =
      kmp_sched_distr_static_chunk_sched_static_chunkone,

  /* Support for OpenMP 4.5 monotonic and nonmonotonic schedule modifiers.
   * Since we need to distinguish the three possible cases (no modifier,
   * monotonic modifier, nonmonotonic modifier), we need separate bits for
   * each modifier. The absence of monotonic does not imply nonmonotonic,
   * especially since 4.5 says that the behaviour of the "no modifier" case
   * is implementation defined in 4.5, but will become "nonmonotonic" in 5.0.
   *
   * Since we're passing a full 32 bit value, we can use a couple of high
   * bits for these flags; out of paranoia we avoid the sign bit.
   *
   * These modifiers can be or-ed into non-static schedules by the compiler
   * to pass the additional information. They will be stripped early in the
   * processing in __kmp_dispatch_init when setting up schedules, so
   * most of the code won't ever see schedules with these bits set.
   */
  kmp_sched_modifier_monotonic = (1 << 29),
  /**< Set if the monotonic schedule modifier was present */
  kmp_sched_modifier_nonmonotonic = (1 << 30),
/**< Set if the nonmonotonic schedule modifier was present */

#define SCHEDULE_WITHOUT_MODIFIERS(s)                                          \
  (enum kmp_sched_t)(                                                          \
      (s) & ~(kmp_sched_modifier_nonmonotonic | kmp_sched_modifier_monotonic))
#define SCHEDULE_HAS_MONOTONIC(s) (((s)&kmp_sched_modifier_monotonic) != 0)
#define SCHEDULE_HAS_NONMONOTONIC(s)                                           \
  (((s)&kmp_sched_modifier_nonmonotonic) != 0)
#define SCHEDULE_HAS_NO_MODIFIERS(s)                                           \
  (((s) & (kmp_sched_modifier_nonmonotonic | kmp_sched_modifier_monotonic)) == \
   0)

} kmp_sched_t;

// parallel defs
typedef void (*kmp_ParFctPtr)(kmp_int32 *global_tid, kmp_int32 *bound_tid, ...);
typedef void (*kmp_ReductFctPtr)(void *lhsData, void *rhsData);
typedef void (*kmp_InterWarpCopyFctPtr)(void *src, kmp_int32 warp_num);
typedef void (*kmp_ShuffleReductFctPtr)(void *rhsData, int16_t lane_id,
                                        int16_t lane_offset,
                                        int16_t shortCircuit);
typedef void (*kmp_CopyToScratchpadFctPtr)(void *reduceData, void *scratchpad,
                                           kmp_int32 index, kmp_int32 width);
typedef void (*kmp_LoadReduceFctPtr)(void *reduceData, void *scratchpad,
                                     kmp_int32 index, kmp_int32 width,
                                     kmp_int32 reduce);

// task defs
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


// task dep defs
#define KMP_TASKDEP_IN 0x1u
#define KMP_TASKDEP_OUT 0x2u
typedef struct kmp_TaskDep_Public {
  void *addr;
  size_t len;
  uint8_t flags; // bit 0: in, bit 1: out
} kmp_TaskDep_Public;

// flags that interpret the interface part of tasking flags
#define KMP_TASK_IS_TIED 0x1
#define KMP_TASK_FINAL 0x2
#define KMP_TASK_MERGED_IF0 0x4 /* unused */
#define KMP_TASK_DESTRUCTOR_THUNK 0x8

// flags for task setup return
#define KMP_CURRENT_TASK_NOT_SUSPENDED 0
#define KMP_CURRENT_TASK_SUSPENDED 1

////////////////////////////////////////////////////////////////////////////////
// flags for kstate (all bits initially off)
////////////////////////////////////////////////////////////////////////////////

// first 2 bits used by kmp_Reduction (defined in kmp_reduction.cpp)
#define KMP_REDUCTION_MASK 0x3
#define KMP_SKIP_NEXT_CALL 0x4
#define KMP_SKIP_NEXT_CANCEL_BARRIER 0x8

////////////////////////////////////////////////////////////////////////////////
// data
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
// external interface
////////////////////////////////////////////////////////////////////////////////

// query
EXTERN kmp_int32 __kmpc_global_num_threads(ident_t *loc); // missing
EXTERN kmp_int32 __kmpc_bound_thread_num(ident_t *loc);   // missing
EXTERN kmp_int32 __kmpc_bound_num_threads(ident_t *loc);  // missing
EXTERN kmp_int32 __kmpc_in_parallel(ident_t *loc);        // missing

// parallel
EXTERN kmp_int32 __kmpc_global_thread_num(ident_t *loc);
EXTERN void __kmpc_push_num_threads(ident_t *loc, kmp_int32 global_tid,
                                    kmp_int32 num_threads);
// simd
EXTERN void __kmpc_push_simd_limit(ident_t *loc, kmp_int32 global_tid,
                                   kmp_int32 simd_limit);
// not supported
EXTERN void __kmpc_fork_call(ident_t *loc, kmp_int32 argc, kmpc_micro microtask, ...);
EXTERN void __kmpc_serialized_parallel(ident_t *loc, kmp_uint32 global_tid);
EXTERN void __kmpc_end_serialized_parallel(ident_t *loc,
                                           kmp_uint32 global_tid);
EXTERN uint16_t __kmpc_parallel_level(ident_t *loc, kmp_uint32 global_tid);

// proc bind
EXTERN void __kmpc_push_proc_bind(ident_t *loc, kmp_uint32 global_tid,
                                  int proc_bind);
EXTERN int omp_get_num_places(void);
EXTERN int omp_get_place_num_procs(int place_num);
EXTERN void omp_get_place_proc_ids(int place_num, int *ids);
EXTERN int omp_get_place_num(void);
EXTERN int omp_get_partition_num_places(void);
EXTERN void omp_get_partition_place_nums(int *place_nums);

// for static (no chunk or chunk)
EXTERN void __kmpc_for_static_init_4(ident_t *loc, kmp_int32 global_tid,
                                     enum sched_type sched, kmp_int32 *plastiter,
                                     kmp_int32 *plower, kmp_int32 *pupper,
                                     kmp_int32 *pstride, kmp_int32 incr,
                                     kmp_int32 chunk);
EXTERN void __kmpc_for_static_init_4u(ident_t *loc, kmp_int32 global_tid,
                                      enum sched_type sched, kmp_int32 *plastiter,
                                      kmp_uint32 *plower, kmp_uint32 *pupper,
                                      kmp_int32 *pstride, kmp_int32 incr,
                                      kmp_int32 chunk);
EXTERN void __kmpc_for_static_init_8(ident_t *loc, kmp_int32 global_tid,
                                     enum sched_type sched, kmp_int32 *plastiter,
                                     kmp_int64 *plower, kmp_int64 *pupper,
                                     kmp_int64 *pstride, kmp_int64 incr,
                                     kmp_int64 chunk);
EXTERN void __kmpc_for_static_init_8u(ident_t *loc, kmp_int32 global_tid,
                                      enum sched_type sched, kmp_int32 *plastiter1,
                                      kmp_uint64 *plower, kmp_uint64 *pupper,
                                      kmp_int64 *pstride, kmp_int64 incr,
                                      kmp_int64 chunk);
EXTERN
void __kmpc_for_static_init_4_simple_spmd(ident_t *loc, kmp_int32 global_tid,
                                          enum sched_type sched, kmp_int32 *plastiter,
                                          kmp_int32 *plower, kmp_int32 *pupper,
                                          kmp_int32 *pstride, kmp_int32 incr,
                                          kmp_int32 chunk);
EXTERN
void __kmpc_for_static_init_4u_simple_spmd(ident_t *loc, kmp_int32 global_tid,
                                           enum sched_type sched, kmp_int32 *plastiter,
                                           kmp_uint32 *plower, kmp_uint32 *pupper,
                                           kmp_int32 *pstride, kmp_int32 incr,
                                           kmp_int32 chunk);
EXTERN
void __kmpc_for_static_init_8_simple_spmd(ident_t *loc, kmp_int32 global_tid,
                                          enum sched_type sched, kmp_int32 *plastiter,
                                          kmp_int64 *plower, kmp_int64 *pupper,
                                          kmp_int64 *pstride, kmp_int64 incr,
                                          kmp_int64 chunk);
EXTERN
void __kmpc_for_static_init_8u_simple_spmd(ident_t *loc, kmp_int32 global_tid,
                                           enum sched_type sched, kmp_int32 *plastiter1,
                                           kmp_uint64 *plower, kmp_uint64 *pupper,
                                           kmp_int64 *pstride, kmp_int64 incr,
                                           kmp_int64 chunk);
EXTERN
void __kmpc_for_static_init_4_simple_generic(ident_t *loc,
                                             kmp_int32 global_tid, enum sched_type sched,
                                             kmp_int32 *plastiter,
                                             kmp_int32 *plower, kmp_int32 *pupper,
                                             kmp_int32 *pstride, kmp_int32 incr,
                                             kmp_int32 chunk);
EXTERN
void __kmpc_for_static_init_4u_simple_generic(
    ident_t *loc, kmp_int32 global_tid, enum sched_type sched, kmp_int32 *plastiter,
    kmp_uint32 *plower, kmp_uint32 *pupper, kmp_int32 *pstride, kmp_int32 incr,
    kmp_int32 chunk);
EXTERN
void __kmpc_for_static_init_8_simple_generic(ident_t *loc,
                                             kmp_int32 global_tid, enum sched_type sched,
                                             kmp_int32 *plastiter,
                                             kmp_int64 *plower, kmp_int64 *pupper,
                                             kmp_int64 *pstride, kmp_int64 incr,
                                             kmp_int64 chunk);
EXTERN
void __kmpc_for_static_init_8u_simple_generic(
    ident_t *loc, kmp_int32 global_tid, enum sched_type sched, kmp_int32 *plastiter1,
    kmp_uint64 *plower, kmp_uint64 *pupper, kmp_int64 *pstride, kmp_int64 incr,
    kmp_int64 chunk);

EXTERN void __kmpc_for_static_fini(ident_t *loc, kmp_int32 global_tid);

// for dynamic
EXTERN void __kmpc_dispatch_init_4(ident_t *loc, kmp_int32 global_tid,
                                   enum sched_type schedule, kmp_int32 lower, kmp_int32 upper,
                                   kmp_int32 incr, kmp_int32 chunk);
EXTERN void __kmpc_dispatch_init_4u(ident_t *loc, kmp_int32 global_tid,
                                    enum sched_type sched, kmp_uint32 lower,
                                    kmp_uint32 upper, kmp_int32 incr,
                                    kmp_int32 chunk);
EXTERN void __kmpc_dispatch_init_8(ident_t *loc, kmp_int32 global_tid,
                                   enum sched_type sched, kmp_int64 lower, kmp_int64 upper,
                                   kmp_int64 incr, kmp_int64 chunk);
EXTERN void __kmpc_dispatch_init_8u(ident_t *loc, kmp_int32 global_tid,
                                    enum sched_type sched, kmp_uint64 lower,
                                    kmp_uint64 upper, kmp_int64 incr,
                                    kmp_int64 chunk);

EXTERN int __kmpc_dispatch_next_4(ident_t *loc, kmp_int32 global_tid,
                                  kmp_int32 *plastiter, kmp_int32 *plower,
                                  kmp_int32 *pupper, kmp_int32 *pstride);
EXTERN int __kmpc_dispatch_next_4u(ident_t *loc, kmp_int32 global_tid,
                                   kmp_int32 *plastiter, kmp_uint32 *plower,
                                   kmp_uint32 *pupper, kmp_int32 *pstride);
EXTERN int __kmpc_dispatch_next_8(ident_t *loc, kmp_int32 global_tid,
                                  kmp_int32 *plastiter, kmp_int64 *plower,
                                  kmp_int64 *pupper, kmp_int64 *pstride);
EXTERN int __kmpc_dispatch_next_8u(ident_t *loc, kmp_int32 global_tid,
                                   kmp_int32 *plastiter, kmp_uint64 *plower,
                                   kmp_uint64 *pupper, kmp_int64 *pstride);

EXTERN void __kmpc_dispatch_fini_4(ident_t *loc, kmp_int32 global_tid);
EXTERN void __kmpc_dispatch_fini_4u(ident_t *loc, kmp_int32 global_tid);
EXTERN void __kmpc_dispatch_fini_8(ident_t *loc, kmp_int32 global_tid);
EXTERN void __kmpc_dispatch_fini_8u(ident_t *loc, kmp_int32 global_tid);

// Support for reducing conditional lastprivate variables
EXTERN void __kmpc_reduce_conditional_lastprivate(ident_t *loc,
                                                  kmp_int32 global_tid,
                                                  kmp_int32 varNum, void *array);

// reduction
EXTERN void __kmpc_nvptx_end_reduce(kmp_int32 global_tid);
EXTERN void __kmpc_nvptx_end_reduce_nowait(kmp_int32 global_tid);
EXTERN kmp_int32 __kmpc_nvptx_parallel_reduce_nowait(
    kmp_int32 global_tid, kmp_int32 num_vars, size_t reduce_size, void *reduce_data,
    kmp_ShuffleReductFctPtr shflFct, kmp_InterWarpCopyFctPtr cpyFct);
EXTERN kmp_int32 __kmpc_nvptx_parallel_reduce_nowait_simple_spmd(
    kmp_int32 global_tid, kmp_int32 num_vars, size_t reduce_size, void *reduce_data,
    kmp_ShuffleReductFctPtr shflFct, kmp_InterWarpCopyFctPtr cpyFct);
EXTERN kmp_int32 __kmpc_nvptx_parallel_reduce_nowait_simple_generic(
    kmp_int32 global_tid, kmp_int32 num_vars, size_t reduce_size, void *reduce_data,
    kmp_ShuffleReductFctPtr shflFct, kmp_InterWarpCopyFctPtr cpyFct);
EXTERN kmp_int32 __kmpc_nvptx_simd_reduce_nowait(
    kmp_int32 global_tid, kmp_int32 num_vars, size_t reduce_size, void *reduce_data,
    kmp_ShuffleReductFctPtr shflFct, kmp_InterWarpCopyFctPtr cpyFct);
EXTERN kmp_int32 __kmpc_nvptx_teams_reduce_nowait(
    kmp_int32 global_tid, kmp_int32 num_vars, size_t reduce_size, void *reduce_data,
    kmp_ShuffleReductFctPtr shflFct, kmp_InterWarpCopyFctPtr cpyFct,
    kmp_CopyToScratchpadFctPtr sratchFct, kmp_LoadReduceFctPtr ldFct);
EXTERN kmp_int32 __kmpc_nvptx_teams_reduce_nowait_simple_spmd(
    kmp_int32 global_tid, kmp_int32 num_vars, size_t reduce_size, void *reduce_data,
    kmp_ShuffleReductFctPtr shflFct, kmp_InterWarpCopyFctPtr cpyFct,
    kmp_CopyToScratchpadFctPtr sratchFct, kmp_LoadReduceFctPtr ldFct);
EXTERN kmp_int32 __kmpc_nvptx_teams_reduce_nowait_simple_generic(
    kmp_int32 global_tid, kmp_int32 num_vars, size_t reduce_size, void *reduce_data,
    kmp_ShuffleReductFctPtr shflFct, kmp_InterWarpCopyFctPtr cpyFct,
    kmp_CopyToScratchpadFctPtr sratchFct, kmp_LoadReduceFctPtr ldFct);
EXTERN kmp_int32 __kmpc_shuffle_int32(kmp_int32 val, int16_t delta, int16_t size);
EXTERN kmp_int64 __kmpc_shuffle_int64(kmp_int64 val, int16_t delta, int16_t size);

// sync barrier
EXTERN void __kmpc_barrier(ident_t *loc_ref, kmp_int32 tid);
EXTERN void __kmpc_barrier_simple_spmd(ident_t *loc_ref, kmp_int32 tid);
EXTERN void __kmpc_barrier_simple_generic(ident_t *loc_ref, kmp_int32 tid);
EXTERN kmp_int32 __kmpc_cancel_barrier(ident_t *loc, kmp_int32 global_tid);

// single
EXTERN kmp_int32 __kmpc_single(ident_t *loc, kmp_int32 global_tid);
EXTERN void __kmpc_end_single(ident_t *loc, kmp_int32 global_tid);

// sync
EXTERN kmp_int32 __kmpc_master(ident_t *loc, kmp_int32 global_tid);
EXTERN void __kmpc_end_master(ident_t *loc, kmp_int32 global_tid);
EXTERN void __kmpc_ordered(ident_t *loc, kmp_int32 global_tid);
EXTERN void __kmpc_end_ordered(ident_t *loc, kmp_int32 global_tid);
EXTERN void __kmpc_critical(ident_t *loc, kmp_int32 global_tid,
                            kmp_critical_name *crit);
EXTERN void __kmpc_end_critical(ident_t *loc, kmp_int32 global_tid,
                                kmp_critical_name *crit);
EXTERN void __kmpc_flush(ident_t *loc);

// vote
EXTERN kmp_int32 __kmpc_warp_active_thread_mask();

// tasks
EXTERN kmp_task_t *__kmpc_omp_task_alloc(ident_t *loc,
                                            kmp_int32 global_tid, kmp_int32 flag,
                                            size_t sizeOfTaskInclPrivate,
                                            size_t sizeOfSharedTable,
                                            kmp_routine_entry_t sub);
EXTERN kmp_int32 __kmpc_omp_task(ident_t *loc, kmp_int32 global_tid,
                               kmp_task_t *newLegacyTaskDescr);
EXTERN kmp_int32 __kmpc_omp_task_with_deps(ident_t *loc, kmp_uint32 global_tid,
                                         kmp_task_t *newLegacyTaskDescr,
                                         kmp_int32 depNum, void *depList,
                                         kmp_int32 noAliasDepNum,
                                         void *noAliasDepList);
EXTERN void __kmpc_omp_task_begin_if0(ident_t *loc, kmp_uint32 global_tid,
                                      kmp_task_t *newLegacyTaskDescr);
EXTERN void __kmpc_omp_task_complete_if0(ident_t *loc, kmp_uint32 global_tid,
                                         kmp_task_t *newLegacyTaskDescr);
EXTERN void __kmpc_omp_wait_deps(ident_t *loc, kmp_uint32 global_tid,
                                 kmp_int32 depNum, void *depList,
                                 kmp_int32 noAliasDepNum, void *noAliasDepList);
EXTERN void __kmpc_taskgroup(ident_t *loc, kmp_uint32 global_tid);
EXTERN void __kmpc_end_taskgroup(ident_t *loc, kmp_uint32 global_tid);
EXTERN kmp_int32 __kmpc_omp_taskyield(ident_t *loc, kmp_uint32 global_tid,
                                    int end_part);
EXTERN kmp_int32 __kmpc_omp_taskwait(ident_t *loc, kmp_uint32 global_tid);
EXTERN void __kmpc_taskloop(ident_t *loc, kmp_uint32 global_tid,
                            kmp_task_t *newKmpTaskDescr, int if_val,
                            kmp_uint64 *lb, kmp_uint64 *ub, kmp_int64 st, int nogroup,
                            enum sched_type sched, kmp_uint64 grainsize, void *task_dup);

// cancel
EXTERN kmp_int32 __kmpc_cancellationpoint(ident_t *loc, kmp_int32 global_tid,
                                        kmp_int32 cancelVal);
EXTERN kmp_int32 __kmpc_cancel(ident_t *loc, kmp_int32 global_tid,
                             kmp_int32 cancelVal);

// non standard
EXTERN void __kmpc_kernel_init_params(void *ReductionScratchpadPtr);
EXTERN void __kmpc_kernel_init(int ThreadLimit, int16_t RequiresOMPRuntime);
EXTERN void __kmpc_kernel_deinit(int16_t IsOMPRuntimeInitialized);
EXTERN void __kmpc_spmd_kernel_init(int ThreadLimit, int16_t RequiresOMPRuntime,
                                    int16_t RequiresDataSharing);
EXTERN void __kmpc_spmd_kernel_deinit();
EXTERN void __kmpc_kernel_prepare_parallel(void *WorkFn,
                                           int16_t IsOMPRuntimeInitialized);
EXTERN bool __kmpc_kernel_parallel(void **WorkFn,
                                   int16_t IsOMPRuntimeInitialized);
EXTERN void __kmpc_kernel_end_parallel();
EXTERN bool __kmpc_kernel_convergent_parallel(void *buffer, kmp_uint32 Mask,
                                              bool *IsFinal,
                                              kmp_int32 *LaneSource);
EXTERN void __kmpc_kernel_end_convergent_parallel(void *buffer);
EXTERN bool __kmpc_kernel_convergent_simd(void *buffer, kmp_uint32 Mask,
                                          bool *IsFinal, kmp_int32 *LaneSource,
                                          kmp_int32 *LaneId, kmp_int32 *NumLanes);
EXTERN void __kmpc_kernel_end_convergent_simd(void *buffer);


EXTERN void __kmpc_data_sharing_init_stack();
EXTERN void __kmpc_data_sharing_init_stack_spmd();
EXTERN void *__kmpc_data_sharing_push_stack(size_t size, int16_t UseSharedMemory);
EXTERN void __kmpc_data_sharing_pop_stack(void *a);
EXTERN void __kmpc_begin_sharing_variables(void ***GlobalArgs, size_t nArgs);
EXTERN void __kmpc_end_sharing_variables();
EXTERN void __kmpc_get_shared_variables(void ***GlobalArgs);

// The slot used for data sharing by the master and worker threads. We use a
// complete (default size version and an incomplete one so that we allow sizes
// greater than the default).
struct __kmpc_data_sharing_slot {
  struct __kmpc_data_sharing_slot *Next;
  struct __kmpc_data_sharing_slot *Prev;
  void *PrevSlotStackPtr;
  void *DataEnd;
  char Data[];
};
EXTERN void
__kmpc_initialize_data_sharing_environment(struct __kmpc_data_sharing_slot *RootS,
                                           size_t InitialDataSize);
EXTERN void *__kmpc_data_sharing_environment_begin(
    struct __kmpc_data_sharing_slot **SavedSharedSlot, void **SavedSharedStack,
    void **SavedSharedFrame, kmp_int32 *SavedActiveThreads,
    size_t SharingDataSize, size_t SharingDefaultDataSize,
    int16_t IsOMPRuntimeInitialized);
EXTERN void __kmpc_data_sharing_environment_end(
    struct __kmpc_data_sharing_slot **SavedSharedSlot, void **SavedSharedStack,
    void **SavedSharedFrame, kmp_int32 *SavedActiveThreads, kmp_int32 IsEntryPoint);

EXTERN void *
__kmpc_get_data_sharing_environment_frame(kmp_int32 SourceThreadID,
                                          int16_t IsOMPRuntimeInitialized);

// SPMD execution mode interrogation function.
EXTERN int8_t __kmpc_is_spmd_exec_mode();


//reduction
EXTERN kmp_int32 __kmpc_reduce( ident_t *loc, kmp_int32 global_tid, \
  kmp_int32 num_vars, size_t reduce_size, void * reduce_data, \
  void (*reduce_func)(void *lhs_data, void *rhs_data), kmp_critical_name *lck);

EXTERN kmp_int32 __kmpc_reduce_nowait( ident_t *loc, kmp_int32 global_tid, \
  kmp_int32 num_vars, size_t reduce_size, void * reduce_data, \
  void (*reduce_func)(void *lhs_data, void *rhs_data), kmp_critical_name *lck);

EXTERN void __kmpc_end_reduce(ident_t *loc, kmp_int32 global_tid, kmp_critical_name *lck);

EXTERN void __kmpc_end_reduce_nowait(ident_t *loc, kmp_int32 global_tid, kmp_critical_name *lck);

#endif
