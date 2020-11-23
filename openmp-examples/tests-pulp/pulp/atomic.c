/*
 * Copyright 2019 ETH Zurich, University of Bologna
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

#include <stdlib.h>

#include "hero-target.h"
#include "test.h"

/***************************************************************************************************
 * Helper Functions
 **************************************************************************************************/

int comp_int32(const void* a_ptr, const void* b_ptr)
{
  const int32_t a = *(int32_t*)a_ptr;
  const int32_t b = *(int32_t*)b_ptr;
  return (a > b) - (a < b);
}

inline static void qsort_int32(void* const ptr, size_t count)
{
  qsort(ptr, count, sizeof(int32_t), comp_int32);
}

inline static int zero()
{
  return 0;
}

inline static int one()
{
  return 1;
}

inline static int thread_num()
{
  return omp_get_thread_num();
}

inline static int neg_thread_num()
{
  return -thread_num();
}

static const int min_max_threshold = -2;
static const int minu_maxu_threshold = 4;


/***************************************************************************************************
 * Checker Functions
 **************************************************************************************************/

static unsigned check_swap(const int32_t* const res, size_t N)
{
  unsigned n_errors = 0;
  for (unsigned i = 1; i < N; ++i) {
    n_errors += condition_or_printf(res[i-1] != res[i],
        "Atomic SWAP with thread IDs must lead to unique values");
  }
  return n_errors;
}

static unsigned check_add(const int32_t* const res, size_t N)
{
  unsigned n_errors = 0;
  for (int i = 0; i < N; ++i) {
    n_errors += condition_or_printf(res[i] == i,
        "Atomic ADD must monotonically increment shared variable");
  }
  return n_errors;
}

static unsigned check_and(const int32_t* const res, size_t N)
{
  unsigned n_errors = 0;
  n_errors += condition_or_printf(res[N-1] == 1, "Atomic AND must return 1 for one thread");
  for (unsigned i = 0; i < N-1; ++i) {
    n_errors += condition_or_printf(res[i] == 0, "Atomic AND must return 0 for all other threads");
  }
  return n_errors;
}

static unsigned check_or(const int32_t* const res, size_t N)
{
  unsigned n_errors = 0;
  n_errors += condition_or_printf(res[0] == 0, "Atomic OR must return 0 for one thread");
  for (unsigned i = 1; i < N; ++i) {
    n_errors += condition_or_printf(res[i] == 1, "Atomic OR must return 1 for all other threads");
  }
  return n_errors;
}

static unsigned check_xor(const int32_t* const res, size_t N)
{
  unsigned n_errors = 0;
  for (unsigned i = 0; i < N; ++i) {
    const int32_t expected = i < N/2 ? 0 : 1;
    n_errors += condition_or_printf(res[i] == expected,
        "Atomic XOR must return %u for half of the threads", expected);
  }
  return n_errors;
}

static unsigned check_max(const int32_t* const res, size_t N)
{
  unsigned n_errors = 0;
  for (unsigned i = 0; i < N; ++i) {
    n_errors += condition_or_printf(res[i] >= min_max_threshold,
        "Atomic MAX must only produce values >= %d", min_max_threshold);
  }
  return n_errors;
}

static unsigned check_maxu(const int32_t* const res, size_t N)
{
  unsigned n_errors = 0;
  for (unsigned i = 0; i < N; ++i) {
    n_errors += condition_or_printf(res[i] >= minu_maxu_threshold,
        "Atomic MAXU must only produce values >= %d", minu_maxu_threshold);
  }
  return n_errors;
}

static unsigned check_min(const int32_t* const res, size_t N)
{
  unsigned n_errors = 0;
  for (unsigned i = 0; i < N; ++i) {
    n_errors += condition_or_printf(res[i] <= min_max_threshold,
        "Atomic MAX must only produce values <= %d", min_max_threshold);
  }
  return n_errors;
}

static unsigned check_minu(const int32_t* const res, size_t N)
{
  unsigned n_errors = 0;
  for (unsigned i = 0; i < N; ++i) {
    n_errors += condition_or_printf(res[i] <= minu_maxu_threshold,
        "Atomic MINU must only produce values <= %u", minu_maxu_threshold);
  }
  return n_errors;
}


/***************************************************************************************************
 * Test Harness
 **************************************************************************************************/

// Execute an atomic transaction on all threads and check its result.
// 1) Initialize the memory at `addr` to `init`.
// 2) Invoke `atomic_fn` on `addr` with `val` in parallel and store the result of each core in an
//    array on the stack (each core has a unique index into the shared array).
// 3) Sort the result array in increasing order.
// 4) Invoke `check_fn` on the sorted result array and return the number of errors it reports.
inline static unsigned check_amo(int32_t* const addr, const int32_t init,
    int32_t (*atomic_fn)(int32_t*, int32_t), int32_t (*val_fn)(void),
    unsigned (*check_fn)(const int32_t*, size_t))
{
  *addr = init;
  const size_t N = pulp_cluster_n_cores();
  int32_t res[N];
  #pragma omp parallel
  {
    res[omp_get_thread_num()] = (*atomic_fn)(addr, (*val_fn)());
  }
  qsort_int32(res, N);

  return (*check_fn)(res, N);
}

// Generic AMO function
typedef int32_t (*amo_fn_t)(int32_t*, int32_t);

// Check all atomic operations for one address.
inline static unsigned check_addr(int32_t* const addr)
{
  unsigned n_errors = 0;

  n_errors += check_amo(addr, 9,                              &hero_atomic_swap, &thread_num,      &check_swap);
  n_errors += check_amo(addr, 0,                              &hero_atomic_add,  &one,             &check_add);
  n_errors += check_amo(addr, 1,                              &hero_atomic_and,  &zero,            &check_and);
  n_errors += check_amo(addr, 0,                              &hero_atomic_or,   &one,             &check_or);
  n_errors += check_amo(addr, 0,                              &hero_atomic_xor,  &one,             &check_xor);
  n_errors += check_amo(addr, min_max_threshold,              &hero_atomic_max,  &neg_thread_num,  &check_max);
  n_errors += check_amo(addr, minu_maxu_threshold,  (amo_fn_t)&hero_atomic_maxu, &thread_num,      &check_maxu);
  n_errors += check_amo(addr, min_max_threshold,              &hero_atomic_min,  &neg_thread_num,  &check_min);
  n_errors += check_amo(addr, minu_maxu_threshold,  (amo_fn_t)&hero_atomic_minu, &thread_num,      &check_minu);

  return n_errors;
}

// Test all atomic operations on a set of addresses.
unsigned test_atomic()
{
  unsigned n_errors = 0;
  printf("Testing atomic transactions on L1 ..\n");
  n_errors += check_addr((__device int32_t*)test_l1_base());
  printf("Testing atomic transactions on aliased L1 ..\n");
  n_errors += check_addr((__device int32_t*)test_l1_alias_base());
  printf("Testing atomic transactions on L1 of other cluster ..\n");
  n_errors += check_addr((__device int32_t*)test_l1_other_base());
  printf("Testing atomic transactions on L2 ..\n");
  n_errors += check_addr((__device int32_t*)test_l2_base());
  // Atomic transactions on DRAM are not implemented yet.
  //printf("Testing atomic transactions on DRAM ..\n");
  //n_errors += check_addr((uint32_t*)test_dram_base());
  return n_errors;
}
