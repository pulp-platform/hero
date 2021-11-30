#include <assert.h>
#include <hero-target.h>
#include "test.h"

inline void local_accesses_kernel() {
  // Addresses are hardcoded to make sure the performance counters measure memory accesses and not
  // pointer arithmetic.  The following assertions ensure that the hardcoded addresses are correct.
  volatile uint32_t* const l1 = (__device uint32_t*)0x1001c000;
  assert(l1 == (uint32_t*)test_l1_base());
  volatile uint32_t* const l1_alias = (__device uint32_t*)0x1b01c000;
  assert(l1_alias == (uint32_t*)test_l1_alias_base());

  // Start counters, do two reads and three writes, and pause counters.
  hero_perf_continue_all();
  const uint32_t foo = *l1;
  const uint32_t bar = *l1_alias;
  *l1 = 123;
  *l1_alias = 6789;
  *l1 = 9076;
  hero_perf_pause_all();

  // Do more reads and writes, which must not be counted.
  const uint32_t sam = *l1_alias;
  const uint32_t ba = *l1;
  *l1_alias = 3014;
  *l1 = 8606;
}

unsigned local_accesses_one_counter(const hero_perf_event_t event, const char* event_suffix,
                                    const unsigned expected) {
  // Allocate counter.
  if (hero_perf_alloc(event) != 0) {
    printf("Error allocating counter for hero_perf_event_%s!\n", event_suffix);
    return 1;
  }

  local_accesses_kernel();

  // Read counter.
  const int64_t actual = hero_perf_read(event);

  // Compare and report result.
  unsigned n_errors =
      condition_or_printf(actual == (int64_t)expected, "hero_perf_event_%s was %d instead of %d",
                          event_suffix, (int32_t)actual, expected);

  // Deallocate counter.
  n_errors +=
      condition_or_printf(hero_perf_dealloc(event) == 0,
                          "Error deallocating counter for hero_perf_event_%s", event_suffix);

  return n_errors;
}

unsigned local_accesses_two_counters(const unsigned expected_loads,
                                     const unsigned expected_stores) {
  // Allocate both counters.
  if (hero_perf_alloc(hero_perf_event_load) != 0) {
    printf("Error allocating counter for hero_perf_event_load!\n");
    return 1;
  }
  if (hero_perf_alloc(hero_perf_event_store) != 0) {
    printf("Error allocating counter for hero_perf_event_store!\n");
    return 1;
  }

  local_accesses_kernel();

  // Read counters.
  const int64_t actual_loads = hero_perf_read(hero_perf_event_load);
  const int64_t actual_stores = hero_perf_read(hero_perf_event_store);

  // Compare and report results.
  unsigned n_errors = condition_or_printf(actual_loads == (int64_t)expected_loads,
                                          "hero_perf_event_load was %d instead of %d",
                                          (int32_t)actual_loads, expected_loads);
  n_errors += condition_or_printf(actual_stores == (int64_t)expected_stores,
                                  "hero_perf_event_store was %d instead of %d",
                                  (int32_t)actual_stores, expected_stores);

  // Deallocate counters.
  n_errors += condition_or_printf(hero_perf_dealloc(hero_perf_event_load) == 0,
                                  "Error deallocating counter for hero_perf_event_load");
  n_errors += condition_or_printf(hero_perf_dealloc(hero_perf_event_store) == 0,
                                  "Error deallocating counter for hero_perf_event_store");

  return n_errors;
}

unsigned local_accesses_cycles_and_instrs(const unsigned max_cycles, const unsigned max_instrs) {
  // Allocate both counters.
  if (hero_perf_alloc(hero_perf_event_cycle) != 0) {
    printf("Error allocating counter for hero_perf_event_cycle!\n");
    return 1;
  }
  if (hero_perf_alloc(hero_perf_event_instr_retired) != 0) {
    printf("Error allocating counter for hero_perf_event_instr_retired!\n");
    return 1;
  }

  local_accesses_kernel();

  // Read counters.
  const int64_t actual_cycle = hero_perf_read(hero_perf_event_cycle);
  const int64_t actual_instr_retired = hero_perf_read(hero_perf_event_instr_retired);

  // Compare and report results.
  unsigned n_errors = 0;
  n_errors += condition_or_printf(
      actual_cycle > 0, "hero_perf_event_cycle (%d) was not larger than 0", (int32_t)actual_cycle);
  n_errors +=
      condition_or_printf(actual_cycle <= max_cycles,
                          "hero_perf_event_cycle (%d) was larger than expected maximum (%d)",
                          (int32_t)actual_cycle, (int32_t)max_cycles);
  n_errors += condition_or_printf(actual_instr_retired > 0,
                                  "hero_perf_event_instr_retired (%d) was not larger than 0",
                                  (int32_t)actual_instr_retired);
  n_errors += condition_or_printf(
      actual_instr_retired <= max_instrs,
      "hero_perf_event_instr_retired (%d) was larger than expected maximum (%d)",
      (int32_t)actual_instr_retired, (int32_t)max_instrs);

  // Deallocate counters.
  n_errors += condition_or_printf(hero_perf_dealloc(hero_perf_event_cycle) == 0,
                                  "Error deallocating counter for hero_perf_event_cycle");
  n_errors += condition_or_printf(hero_perf_dealloc(hero_perf_event_instr_retired) == 0,
                                  "Error deallocating counter for hero_perf_event_instr_retired");

  return n_errors;
}

unsigned local_accesses() {
  unsigned n_errors = 0;
  n_errors += local_accesses_one_counter(hero_perf_event_load, "load", 2);
  n_errors += local_accesses_one_counter(hero_perf_event_store, "store", 3);
  n_errors += local_accesses_two_counters(2, 3);
  n_errors += local_accesses_cycles_and_instrs(80, 16);
  return n_errors;
}

inline void external_accesses_kernel() {
  // Addresses are hardcoded to make sure the performance counters measure memory accesses and not
  // pointer arithmetic.  The following assertions ensure that the hardcoded addresses are correct.
  volatile uint32_t* const l1 = (__device uint32_t*)0x1001c000;
  assert(l1 == (uint32_t*)test_l1_base());
  volatile uint32_t* const l2 = (__device uint32_t*)0x1c01f000;
  assert(l2 == (uint32_t*)test_l2_base());
  volatile __host uint32_t* const dram = (__host uint32_t*)0x80000000;
  assert(dram == (__host uint32_t*)test_dram_base());

  // Start counters.
  hero_perf_continue_all();

  // Do some memory accesses, which give rise to loads and stores as follows:
  //
  // | Memory access | loads | of which external | stores | of which external |
  // |:--------------|------:|------------------:|-------:|------------------:|
  // | 1 L1 read     |     1 |                 0 |      0 |                 0 |
  // | 2 L2 reads    |     2 |                 2 |      0 |                 0 |
  // | 2 DRAM reads  | 2*2=4 |             2*1=2 |  2*1=2 |                 0 |
  // |---------------|-------|-------------------|--------|-------------------|
  // | 1 L1 write    |     0 |                 0 |      1 |                 0 |
  // | 4 L2 writes   |     0 |                 0 |      4 |                 4 |
  // | 2 DRAM writes | 2*1=2 |                 0 |  2*2=4 |             2*1=2 |
  // |---------------|-------|-------------------|--------|-------------------|
  // | Total         |     9 |                 4 |     11 |                 6 |
  //
  // The reason each DRAM read and write gives rise to 1 local store and 1 local load in addition to
  // the external load or store is the write to the address extension register and the load from the
  // memory access check register.
  const uint32_t foo = *l2;
  const uint32_t bar = *dram;
  const uint32_t some = *l1;
  const uint32_t bugu = *dram;
  const uint32_t bla = *l2;
  *l2 = 123;
  *dram = 6789;
  *l1 = 4578;
  *l2 = 9076;
  *l2 = 321;
  *dram = 9876;
  *l2 = 6709;

  // Pause counters.
  hero_perf_pause_all();

  // Do more reads and writes, which must not be counted.
  const uint32_t sam = *dram;
  const uint32_t ba = *l2;
  *dram = 3014;
  *l2 = 8606;
}

// Type of comparison function
// - Arguments:
//   1. actual value
//   2. expected value
//   3. event suffix
// - Returns the number of errors in the comparison.
typedef unsigned (*cmp_fn_t)(int64_t, int64_t, const __device char* const);

unsigned external_accesses_one_counter(const hero_perf_event_t event, const char* event_suffix,
                                       const unsigned expected, cmp_fn_t cmp) {
  // Initialize pointer to L1, L2, and DRAM.
  volatile uint32_t* const l1 = (volatile __device uint32_t*)test_l1_base();
  volatile uint32_t* const l2 = (volatile __device uint32_t*)test_l2_base();
  volatile __host uint32_t* const dram = (volatile __host uint32_t*)test_dram_base();

  // Allocate counter.
  if (hero_perf_alloc(event) != 0) {
    printf("Error allocating counter for hero_perf_event_%s!\n", event_suffix);
    return 1;
  }

  external_accesses_kernel();

  // Read counter.
  const int64_t actual = hero_perf_read(event);

  // Compare and report result.
  unsigned n_errors = cmp(actual, (int64_t)expected, event_suffix);

  // Deallocate counter.
  n_errors +=
      condition_or_printf(hero_perf_dealloc(event) == 0,
                          "Error deallocating counter for hero_perf_event_%s", event_suffix);

  return n_errors;
}

unsigned external_accesses_two_counters(const hero_perf_event_t event1, const char* event1_suffix,
                                        const unsigned expected1, cmp_fn_t cmp1,
                                        const hero_perf_event_t event2, const char* event2_suffix,
                                        const unsigned expected2, cmp_fn_t cmp2) {
  // Allocate counters.
  if (hero_perf_alloc(event1) != 0) {
    printf("Error allocating counter for hero_perf_event_%s!\n", event1_suffix);
    return 1;
  }
  if (hero_perf_alloc(event2) != 0) {
    printf("Error allocating counter for hero_perf_event_%s!\n", event2_suffix);
    return 1;
  }

  external_accesses_kernel();

  // Read counters.
  const int64_t actual1 = hero_perf_read(event1);
  const int64_t actual2 = hero_perf_read(event2);

  // Compare and report results.
  unsigned n_errors = 0;
  n_errors += cmp1(actual1, (int64_t)expected1, event1_suffix);
  n_errors += cmp2(actual2, (int64_t)expected2, event2_suffix);

  // Deallocate counters.
  n_errors +=
      condition_or_printf(hero_perf_dealloc(event1) == 0,
                          "Error deallocating counter for hero_perf_event_%s", event1_suffix);
  n_errors +=
      condition_or_printf(hero_perf_dealloc(event2) == 0,
                          "Error deallocating counter for hero_perf_event_%s", event2_suffix);

  return n_errors;
}

// Assert that the actual value equals the expected value.
unsigned cmp_eq(const int64_t actual, const int64_t expected, const __device char* const suffix) {
  return condition_or_printf(actual == expected, "hero_perf_event_%s was %d instead of %d", suffix,
                             (int32_t)actual, (int32_t)expected);
}

// Assert that the actual value is within 10% of the expected value.
unsigned cmp_within_10pct(const int64_t actual, const int64_t expected, const __device char* const suffix) {
  const int64_t expected_plus_10pct = (int64_t)((float)expected * 1.1);
  const int64_t expected_minus_10pct = (int64_t)((float)expected * 0.9);
  unsigned n_errors = 0;
  n_errors += condition_or_printf(actual <= expected_plus_10pct,
                                  "hero_perf_event_%s was %d instead of at most %d", suffix,
                                  (int32_t)actual, (int32_t)expected_plus_10pct);
  n_errors += condition_or_printf(actual >= expected_minus_10pct,
                                  "hero_perf_event_%s was %d instead of at least %d", suffix,
                                  (int32_t)actual, (int32_t)expected_minus_10pct);
  return n_errors;
}

unsigned external_accesses(void) {
  unsigned n_errors = 0;
  n_errors +=
      external_accesses_one_counter(hero_perf_event_load_external, "load_external", 4, &cmp_eq);
  n_errors += external_accesses_one_counter(hero_perf_event_load, "load", 9, &cmp_eq);
  n_errors +=
      external_accesses_one_counter(hero_perf_event_store_external, "store_external", 6, &cmp_eq);
  n_errors += external_accesses_one_counter(hero_perf_event_store, "store", 11, &cmp_eq);
  n_errors += external_accesses_two_counters(hero_perf_event_load_external, "load_external", 4,
                                             &cmp_eq, hero_perf_event_load, "load", 9, &cmp_eq);
  n_errors +=
      external_accesses_two_counters(hero_perf_event_load_external, "load_external", 4, &cmp_eq,
                                     hero_perf_event_store_external, "store_external", 6, &cmp_eq);
  n_errors +=
      external_accesses_two_counters(hero_perf_event_store, "store", 11, &cmp_eq,
                                     hero_perf_event_load_external, "load_external", 4, &cmp_eq);
  n_errors += external_accesses_two_counters(hero_perf_event_store_external, "store_external", 6,
                                             &cmp_eq, hero_perf_event_instr_retired,
                                             "instr_retired", 45, &cmp_within_10pct);

  return n_errors;
}

unsigned test_perf(void) {

  if (hero_rt_core_id() != 0) {
    return 0;
  }

  const int init = hero_perf_init();
  if (init != 0) {
    printf("Error initializing performance measurement: %d!\n", init);
    return 1;
  }

  unsigned n_errors = 0;

  n_errors += local_accesses();
  n_errors += external_accesses();

  hero_perf_deinit();

  return n_errors;
}
