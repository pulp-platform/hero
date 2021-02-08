#include <hero-target.h>
#include "test.h"

unsigned local_accesses(void)
{
  // Initialize pointer to L1 (and alias) and allocate counters.
  volatile uint32_t* const l1 = (volatile __device uint32_t*)test_l1_base();
  volatile uint32_t* const l1_alias = (volatile __device uint32_t*)test_l1_alias_base();
  unsigned n_errors = 0;
  if (hero_perf_alloc(hero_perf_event_load) != 0) {
    printf("Error allocating counter for loads!\n");
    n_errors += 1;
    goto __ret;
  }
  if (hero_perf_alloc(hero_perf_event_store) != 0) {
    printf("Error allocating counter for stores!\n");
    n_errors += 1;
    goto __dealloc_loads;
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

  // Read counters.
  const uint32_t load_local = hero_perf_read(hero_perf_event_load);
  const uint32_t store_local = hero_perf_read(hero_perf_event_store);

  // Evaluate result.
  n_errors += condition_or_printf(load_local == 2,
      "hero_perf_event_load_local was %d instead of 2", load_local);
  n_errors += condition_or_printf(store_local == 3,
      "hero_perf_event_store_local was %d instead of 3", store_local);

  // Deallocate counters.
  n_errors += condition_or_printf(hero_perf_dealloc(hero_perf_event_store) == 0,
      "Error deallocating counter for stores");
__dealloc_loads:
  n_errors += condition_or_printf(hero_perf_dealloc(hero_perf_event_load) == 0,
      "Error deallocating counter for loads");

__ret:
  return n_errors;
}

unsigned external_accesses(void)
{
  // Initialize pointer to L1, L2, and DRAM and allocate counters.
  volatile uint32_t* const l1 = (volatile __device uint32_t*)test_l1_base();
  volatile uint32_t* const l2 = (volatile __device uint32_t*)test_l2_base();
  volatile uint32_t* const dram = (volatile __device uint32_t*)test_dram_base();
  unsigned n_errors = 0;
  if (hero_perf_alloc(hero_perf_event_load) != 0) {
    printf("Error allocating counter for loads!\n");
    n_errors += 1;
    goto __ret;
  }
  if (hero_perf_alloc(hero_perf_event_store) != 0) {
    printf("Error allocating counter for stores!\n");
    n_errors += 1;
    goto __dealloc_loads;
  }
  if (hero_perf_alloc(hero_perf_event_load_external) != 0) {
    printf("Error allocating counter for external loads!\n");
    n_errors += 1;
    goto __dealloc_stores_and_loads;
  }
  if (hero_perf_alloc(hero_perf_event_store_external) != 0) {
    printf("Error allocating counter for external stores!\n");
    n_errors += 1;
    goto __dealloc_external_loads_and_stores_and_loads;
  }

  // Start counters, do five reads, of which four are external, and seven writes, of which six are
  // external, and pause counters.
  hero_perf_continue_all();
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
  hero_perf_pause_all();

  // Do more reads and writes, which must not be counted.
  const uint32_t sam = *dram;
  const uint32_t ba = *l2;
  *dram = 3014;
  *l2 = 8606;

  // Read counters.
  const uint32_t load = hero_perf_read(hero_perf_event_load);
  const uint32_t store = hero_perf_read(hero_perf_event_store);
  const uint32_t load_external = hero_perf_read(hero_perf_event_load_external);
  const uint32_t store_external = hero_perf_read(hero_perf_event_store_external);

  // Evaluate result.
  n_errors += condition_or_printf(load_external == 4,
      "hero_perf_event_load_external was %d instead of 4", load_external);
  n_errors += condition_or_printf(load == 5,
      "hero_perf_event_load was %d instead of 5", load);
  n_errors += condition_or_printf(store_external == 6,
      "hero_perf_event_store_external was %d instead of 6", store_external);
  n_errors += condition_or_printf(store == 7,
      "hero_perf_event_store was %d instead of 7", store);

  // Deallocate counters.
  n_errors += condition_or_printf(hero_perf_dealloc(hero_perf_event_store_external) == 0,
      "Error deallocating counter for external stores");
__dealloc_external_loads_and_stores_and_loads:
  n_errors += condition_or_printf(hero_perf_dealloc(hero_perf_event_load_external) == 0,
      "Error deallocating counter for external loads");
__dealloc_stores_and_loads:
  n_errors += condition_or_printf(hero_perf_dealloc(hero_perf_event_store) == 0,
      "Error deallocating counter for stores");
__dealloc_loads:
  n_errors += condition_or_printf(hero_perf_dealloc(hero_perf_event_load) == 0,
      "Error deallocating counter for loads");

__ret:
  return n_errors;
}

unsigned test_perf(void)
{

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
