#include <hero-target.h>
#include "test.h"

unsigned _local_accesses(const hero_perf_event_t event, const char* event_suffix,
                         const unsigned expected) {
  // Initialize pointer to L1 and L1 alias.
  volatile uint32_t* const l1 = (volatile __device uint32_t*)test_l1_base();
  volatile uint32_t* const l1_alias = (volatile __device uint32_t*)test_l1_alias_base();

  // Allocate counter.
  if (hero_perf_alloc(event) != 0) {
    printf("Error allocating counter for hero_perf_event_%s!\n", event_suffix);
    return 1;
  }

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

  // Read counter.
  const int64_t actual = hero_perf_read(event);

  // Compare and report result.
  unsigned n_errors =
      condition_or_printf(actual == (int64_t)expected, "hero_perf_event_%s was %d instead of %d",
                          event_suffix, actual, expected);

  // Deallocate counter.
  n_errors +=
      condition_or_printf(hero_perf_dealloc(event) == 0,
                          "Error deallocating counter for hero_perf_event_%s", event_suffix);

  return n_errors;
}

unsigned local_accesses() {
  unsigned n_errors = 0;
  n_errors += _local_accesses(hero_perf_event_load, "load", 2);
  n_errors += _local_accesses(hero_perf_event_store, "store", 3);
  return n_errors;
}

unsigned _external_accesses(const hero_perf_event_t event, const char* event_suffix,
                            const unsigned expected) {
  // Initialize pointer to L1, L2, and DRAM.
  volatile uint32_t* const l1 = (volatile __device uint32_t*)test_l1_base();
  volatile uint32_t* const l2 = (volatile __device uint32_t*)test_l2_base();
  volatile __host uint32_t* const dram = (volatile __host uint32_t*)test_dram_base();

  // Allocate counter.
  if (hero_perf_alloc(event) != 0) {
    printf("Error allocating counter for hero_perf_event_%s!\n", event_suffix);
    return 1;
  }

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

  // Read counter.
  const int64_t actual = hero_perf_read(event);

  // Compare and report result.
  unsigned n_errors =
      condition_or_printf(actual == (int64_t)expected, "hero_perf_event_%s was %d instead of %d",
                          event_suffix, actual, expected);

  // Deallocate counter.
  n_errors +=
      condition_or_printf(hero_perf_dealloc(event) == 0,
                          "Error deallocating counter for hero_perf_event_%s", event_suffix);

  return n_errors;
}

unsigned external_accesses(void) {
  unsigned n_errors = 0;
  n_errors += _external_accesses(hero_perf_event_load_external, "load_external", 4);
  n_errors += _external_accesses(hero_perf_event_load, "load", 9);
  n_errors += _external_accesses(hero_perf_event_store_external, "store_external", 6);
  n_errors += _external_accesses(hero_perf_event_store, "store", 11);

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

  hero_perf_term();

  return n_errors;
}
