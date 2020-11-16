#ifndef __RT_USE_ASSERT
#define __RT_USE_ASSERT
#endif
#include <rt/rt_debug.h>

#include "interface.h"

static void __kmpc_not_implemented() {
    rt_assert(false, "kmpc function not implemented\n");
    abort();
}

// for debug
void __kmpc_print_str(char *title) { __kmpc_not_implemented(); }
void __kmpc_print_title_int(char *title, int data) { __kmpc_not_implemented(); }
void __kmpc_print_index(char *title, int i) { __kmpc_not_implemented(); }
void __kmpc_print_int(int data) { __kmpc_not_implemented(); }
void __kmpc_print_double(double data) { __kmpc_not_implemented(); }
void __kmpc_print_address_int64(kmp_int64 data) { __kmpc_not_implemented(); }

// query
kmp_int32 __kmpc_global_num_threads(ident_t *loc) { __kmpc_not_implemented(); return 0; } // missing
kmp_int32 __kmpc_bound_thread_num(ident_t *loc) { __kmpc_not_implemented(); return 0; }   // missing
kmp_int32 __kmpc_bound_num_threads(ident_t *loc) { __kmpc_not_implemented(); return 0; }  // missing
kmp_int32 __kmpc_in_parallel(ident_t *loc) { __kmpc_not_implemented(); return 0; }        // missing

// simd
void __kmpc_push_simd_limit(ident_t *loc, kmp_int32 global_tid,
                                   kmp_int32 simd_limit) { __kmpc_not_implemented(); }

// aee
void __kmpc_serialized_parallel(ident_t *loc, kmp_uint32 global_tid) { __kmpc_not_implemented(); }
void __kmpc_end_serialized_parallel(ident_t *loc,
                                           kmp_uint32 global_tid) { __kmpc_not_implemented(); }
uint16_t __kmpc_parallel_level(ident_t *loc, kmp_uint32 global_tid) { __kmpc_not_implemented(); return 0; }

// proc bind
void __kmpc_push_proc_bind(ident_t *loc, kmp_uint32 global_tid,
                                  int proc_bind) { __kmpc_not_implemented(); }

void __kmpc_for_static_init_4_simple_spmd(ident_t *loc, kmp_int32 global_tid,
                                          enum sched_type sched, kmp_int32 *plastiter,
                                          kmp_int32 *plower, kmp_int32 *pupper,
                                          kmp_int32 *pstride, kmp_int32 incr,
                                          kmp_int32 chunk) { __kmpc_not_implemented(); }
void __kmpc_for_static_init_4u_simple_spmd(ident_t *loc, kmp_int32 global_tid,
                                           enum sched_type sched, kmp_int32 *plastiter,
                                           kmp_uint32 *plower, kmp_uint32 *pupper,
                                           kmp_int32 *pstride, kmp_int32 incr,
                                           kmp_int32 chunk) { __kmpc_not_implemented(); }
void __kmpc_for_static_init_8_simple_spmd(ident_t *loc, kmp_int32 global_tid,
                                          enum sched_type sched, kmp_int32 *plastiter,
                                          kmp_int64 *plower, kmp_int64 *pupper,
                                          kmp_int64 *pstride, kmp_int64 incr,
                                          kmp_int64 chunk) { __kmpc_not_implemented(); }
void __kmpc_for_static_init_8u_simple_spmd(ident_t *loc, kmp_int32 global_tid,
                                           enum sched_type sched, kmp_int32 *plastiter1,
                                           kmp_uint64 *plower, kmp_uint64 *pupper,
                                           kmp_int64 *pstride, kmp_int64 incr,
                                           kmp_int64 chunk) { __kmpc_not_implemented(); }
void __kmpc_for_static_init_4_simple_generic(ident_t *loc,
                                             kmp_int32 global_tid, enum sched_type sched,
                                             kmp_int32 *plastiter,
                                             kmp_int32 *plower, kmp_int32 *pupper,
                                             kmp_int32 *pstride, kmp_int32 incr,
                                             kmp_int32 chunk) { __kmpc_not_implemented(); }
void __kmpc_for_static_init_4u_simple_generic(
    ident_t *loc, kmp_int32 global_tid, enum sched_type sched, kmp_int32 *plastiter,
    kmp_uint32 *plower, kmp_uint32 *pupper, kmp_int32 *pstride, kmp_int32 incr,
    kmp_int32 chunk) { __kmpc_not_implemented(); }
void __kmpc_for_static_init_8_simple_generic(ident_t *loc,
                                             kmp_int32 global_tid, enum sched_type sched,
                                             kmp_int32 *plastiter,
                                             kmp_int64 *plower, kmp_int64 *pupper,
                                             kmp_int64 *pstride, kmp_int64 incr,
                                             kmp_int64 chunk) { __kmpc_not_implemented(); }
void __kmpc_for_static_init_8u_simple_generic(
    ident_t *loc, kmp_int32 global_tid, enum sched_type sched, kmp_int32 *plastiter1,
    kmp_uint64 *plower, kmp_uint64 *pupper, kmp_int64 *pstride, kmp_int64 incr,
    kmp_int64 chunk) { __kmpc_not_implemented(); }


// for dynamic
void __kmpc_dispatch_init_4u(ident_t *loc, kmp_int32 global_tid,
                                    enum sched_type sched, kmp_uint32 lower,
                                    kmp_uint32 upper, kmp_int32 incr,
                                    kmp_int32 chunk) { __kmpc_not_implemented(); }
void __kmpc_dispatch_init_8(ident_t *loc, kmp_int32 global_tid,
                                   enum sched_type sched, kmp_int64 lower, kmp_int64 upper,
                                   kmp_int64 incr, kmp_int64 chunk) { __kmpc_not_implemented(); }
int __kmpc_dispatch_next_4u(ident_t *loc, kmp_int32 global_tid,
                                   kmp_int32 *plastiter, kmp_uint32 *plower,
                                   kmp_uint32 *pupper, kmp_int32 *pstride) { __kmpc_not_implemented(); return 0; }
int __kmpc_dispatch_next_8(ident_t *loc, kmp_int32 global_tid,
                                  kmp_int32 *plastiter, kmp_int64 *plower,
                                  kmp_int64 *pupper, kmp_int64 *pstride) { __kmpc_not_implemented(); return 0; }

void __kmpc_dispatch_fini_4(ident_t *loc, kmp_int32 global_tid) { __kmpc_not_implemented(); }
void __kmpc_dispatch_fini_4u(ident_t *loc, kmp_int32 global_tid) { __kmpc_not_implemented(); }
void __kmpc_dispatch_fini_8(ident_t *loc, kmp_int32 global_tid) { __kmpc_not_implemented(); }
void __kmpc_dispatch_fini_8u(ident_t *loc, kmp_int32 global_tid) { __kmpc_not_implemented(); }

// Support for reducing conditional lastprivate variables
void __kmpc_reduce_conditional_lastprivate(ident_t *loc,
                                                  kmp_int32 global_tid,
                                                  kmp_int32 varNum, void *array) { __kmpc_not_implemented(); }

// reduction
void __kmpc_nvptx_end_reduce(kmp_int32 global_tid) { __kmpc_not_implemented(); }
void __kmpc_nvptx_end_reduce_nowait(kmp_int32 global_tid) { __kmpc_not_implemented(); }
kmp_int32 __kmpc_nvptx_parallel_reduce_nowait(
    kmp_int32 global_tid, kmp_int32 num_vars, size_t reduce_size, void *reduce_data,
    kmp_ShuffleReductFctPtr shflFct, kmp_InterWarpCopyFctPtr cpyFct) { __kmpc_not_implemented(); return 0; }
kmp_int32 __kmpc_nvptx_parallel_reduce_nowait_simple_spmd(
    kmp_int32 global_tid, kmp_int32 num_vars, size_t reduce_size, void *reduce_data,
    kmp_ShuffleReductFctPtr shflFct, kmp_InterWarpCopyFctPtr cpyFct) { __kmpc_not_implemented(); return 0; }
kmp_int32 __kmpc_nvptx_parallel_reduce_nowait_simple_generic(
    kmp_int32 global_tid, kmp_int32 num_vars, size_t reduce_size, void *reduce_data,
    kmp_ShuffleReductFctPtr shflFct, kmp_InterWarpCopyFctPtr cpyFct) { __kmpc_not_implemented(); return 0; }
kmp_int32 __kmpc_nvptx_simd_reduce_nowait(
    kmp_int32 global_tid, kmp_int32 num_vars, size_t reduce_size, void *reduce_data,
    kmp_ShuffleReductFctPtr shflFct, kmp_InterWarpCopyFctPtr cpyFct) { __kmpc_not_implemented(); return 0; }
kmp_int32 __kmpc_nvptx_teams_reduce_nowait(
    kmp_int32 global_tid, kmp_int32 num_vars, size_t reduce_size, void *reduce_data,
    kmp_ShuffleReductFctPtr shflFct, kmp_InterWarpCopyFctPtr cpyFct,
    kmp_CopyToScratchpadFctPtr sratchFct, kmp_LoadReduceFctPtr ldFct) { __kmpc_not_implemented(); return 0; }
kmp_int32 __kmpc_nvptx_teams_reduce_nowait_simple_spmd(
    kmp_int32 global_tid, kmp_int32 num_vars, size_t reduce_size, void *reduce_data,
    kmp_ShuffleReductFctPtr shflFct, kmp_InterWarpCopyFctPtr cpyFct,
    kmp_CopyToScratchpadFctPtr sratchFct, kmp_LoadReduceFctPtr ldFct) { __kmpc_not_implemented(); return 0; }
kmp_int32 __kmpc_nvptx_teams_reduce_nowait_simple_generic(
    kmp_int32 global_tid, kmp_int32 num_vars, size_t reduce_size, void *reduce_data,
    kmp_ShuffleReductFctPtr shflFct, kmp_InterWarpCopyFctPtr cpyFct,
    kmp_CopyToScratchpadFctPtr sratchFct, kmp_LoadReduceFctPtr ldFct) { __kmpc_not_implemented(); return 0; }
kmp_int32 __kmpc_shuffle_int32(kmp_int32 val, int16_t delta, int16_t size) { __kmpc_not_implemented(); return 0; }
kmp_int64 __kmpc_shuffle_int64(kmp_int64 val, int16_t delta, int16_t size) { __kmpc_not_implemented(); return 0; }

// sync barrier
void __kmpc_barrier_simple_spmd(ident_t *loc_ref, kmp_int32 tid) { __kmpc_not_implemented(); }
void __kmpc_barrier_simple_generic(ident_t *loc_ref, kmp_int32 tid) { __kmpc_not_implemented(); }

// sync
void __kmpc_ordered(ident_t *loc, kmp_int32 global_tid) { __kmpc_not_implemented(); }
void __kmpc_end_ordered(ident_t *loc, kmp_int32 global_tid) { __kmpc_not_implemented(); }

// vote
kmp_int32 __kmpc_warp_active_thread_mask() { __kmpc_not_implemented(); return 0; }

// tasks
kmp_int32 __kmpc_omp_task_with_deps(ident_t *loc, kmp_uint32 global_tid,
                                         kmp_task_t *newLegacyTaskDescr,
                                         kmp_int32 depNum, void *depList,
                                         kmp_int32 noAliasDepNum,
                                         void *noAliasDepList) { __kmpc_not_implemented(); return 0; }
void __kmpc_omp_task_begin_if0(ident_t *loc, kmp_uint32 global_tid,
                                      kmp_task_t *newLegacyTaskDescr) { __kmpc_not_implemented(); }
void __kmpc_omp_task_complete_if0(ident_t *loc, kmp_uint32 global_tid,
                                         kmp_task_t *newLegacyTaskDescr) { __kmpc_not_implemented(); }
void __kmpc_omp_wait_deps(ident_t *loc, kmp_uint32 global_tid,
                                 kmp_int32 depNum, void *depList,
                                 kmp_int32 noAliasDepNum, void *noAliasDepList) { __kmpc_not_implemented(); }
void __kmpc_taskgroup(ident_t *loc, kmp_uint32 global_tid) { __kmpc_not_implemented(); }
void __kmpc_end_taskgroup(ident_t *loc, kmp_uint32 global_tid) { __kmpc_not_implemented(); }
kmp_int32 __kmpc_omp_taskyield(ident_t *loc, kmp_uint32 global_tid,
                                    int end_part) { __kmpc_not_implemented(); return 0; }
kmp_int32 __kmpc_omp_taskwait(ident_t *loc, kmp_uint32 global_tid) { __kmpc_not_implemented(); return 0; }
void __kmpc_taskloop(ident_t *loc, kmp_uint32 global_tid,
                            kmp_task_t *newKmpTaskDescr, int if_val,
                            kmp_uint64 *lb, kmp_uint64 *ub, kmp_int64 st, int nogroup,
                            enum sched_type sched, kmp_uint64 grainsize, void *task_dup) { __kmpc_not_implemented(); }

// cancel
kmp_int32 __kmpc_cancellationpoint(ident_t *loc, kmp_int32 global_tid,
                                        kmp_int32 cancelVal) { __kmpc_not_implemented(); return 0; }
kmp_int32 __kmpc_cancel(ident_t *loc, kmp_int32 global_tid,
                             kmp_int32 cancelVal) { __kmpc_not_implemented(); return 0; }

// non standard
void __kmpc_kernel_prepare_parallel(void *WorkFn,
                                           int16_t IsOMPRuntimeInitialized) { __kmpc_not_implemented(); }
bool __kmpc_kernel_parallel(void **WorkFn,
                                   int16_t IsOMPRuntimeInitialized) { __kmpc_not_implemented(); return 0; }
void __kmpc_kernel_end_parallel() { __kmpc_not_implemented(); }
bool __kmpc_kernel_convergent_parallel(void *buffer, kmp_uint32 Mask,
                                              bool *IsFinal,
                                              kmp_int32 *LaneSource) { __kmpc_not_implemented(); return 0; }
void __kmpc_kernel_end_convergent_parallel(void *buffer) { __kmpc_not_implemented(); }
bool __kmpc_kernel_convergent_simd(void *buffer, kmp_uint32 Mask,
                                          bool *IsFinal, kmp_int32 *LaneSource,
                                          kmp_int32 *LaneId, kmp_int32 *NumLanes) { __kmpc_not_implemented(); return 0; }
void __kmpc_kernel_end_convergent_simd(void *buffer) { __kmpc_not_implemented(); }


void __kmpc_data_sharing_init_stack() { __kmpc_not_implemented(); }
void __kmpc_data_sharing_init_stack_spmd() { __kmpc_not_implemented(); }
void *__kmpc_data_sharing_push_stack(size_t size, int16_t UseSharedMemory) { __kmpc_not_implemented(); return 0; }
void __kmpc_data_sharing_pop_stack(void *a) { __kmpc_not_implemented(); }
void __kmpc_begin_sharing_variables(void ***GlobalArgs, size_t nArgs) { __kmpc_not_implemented(); }
void __kmpc_end_sharing_variables() { __kmpc_not_implemented(); }
void __kmpc_get_shared_variables(void ***GlobalArgs) { __kmpc_not_implemented(); }

void
__kmpc_initialize_data_sharing_environment(struct __kmpc_data_sharing_slot *RootS,
                                           size_t InitialDataSize) { __kmpc_not_implemented(); }
void *__kmpc_data_sharing_environment_begin(
    struct __kmpc_data_sharing_slot **SavedSharedSlot, void **SavedSharedStack,
    void **SavedSharedFrame, kmp_int32 *SavedActiveThreads,
    size_t SharingDataSize, size_t SharingDefaultDataSize,
    int16_t IsOMPRuntimeInitialized) { __kmpc_not_implemented(); return 0; }
void __kmpc_data_sharing_environment_end(
    struct __kmpc_data_sharing_slot **SavedSharedSlot, void **SavedSharedStack,
    void **SavedSharedFrame, kmp_int32 *SavedActiveThreads, kmp_int32 IsEntryPoint) { __kmpc_not_implemented(); }

void *
__kmpc_get_data_sharing_environment_frame(kmp_int32 SourceThreadID,
                                          int16_t IsOMPRuntimeInitialized) { __kmpc_not_implemented(); return 0; }

// other, symbols only
void __kmpc_push_num_teams() { __kmpc_not_implemented(); }
void __kmpc_fork_teams() { __kmpc_not_implemented(); }
