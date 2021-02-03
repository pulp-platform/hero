#include <hero-target.h>
#include "test.h"

unsigned local_accesses(void)
{
  // Initialize pointer to L1 (and alias) and reset counters.
  volatile uint32_t* const l1 = (volatile __device uint32_t*)test_l1_base();
  volatile uint32_t* const l1_alias = (volatile __device uint32_t*)test_l1_alias_base();
  hero_perf_reset(hero_perf_event_load_local);
  hero_perf_reset(hero_perf_event_store_local);

  // Start counters, do two reads and three writes, and stop counters.
  hero_perf_continue(hero_perf_event_load_local);
  hero_perf_continue(hero_perf_event_store_local);
  const uint32_t foo = *l1;
  const uint32_t bar = *l1_alias;
  *l1 = 123;
  *l1_alias = 6789;
  *l1 = 9076;
  hero_perf_pause(hero_perf_event_load_local);
  hero_perf_pause(hero_perf_event_store_local);

  // Do more reads and writes, which must not be counted.
  const uint32_t sam = *l1_alias;
  const uint32_t ba = *l1;
  *l1_alias = 3014;
  *l1 = 8606;

  // Read counters.
  const uint32_t load_local = hero_perf_read(hero_perf_event_load_local);
  const uint32_t store_local = hero_perf_read(hero_perf_event_store_local);

  // Evaluate result.
  unsigned n_errors = 0;
  n_errors += condition_or_printf(load_local == 2,
      "hero_perf_event_load_local was %d instead of 2", load_local);
  n_errors += condition_or_printf(store_local == 3,
      "hero_perf_event_store_local was %d instead of 3", store_local);

  return n_errors;
}

unsigned external_accesses(void)
{
  // Initialize pointer to L2 and DRAM and reset counters.
  volatile uint32_t* const l2 = (volatile __device uint32_t*)test_l2_base();
  volatile uint32_t* const dram = (volatile __device uint32_t*)test_dram_base();
  hero_perf_reset(hero_perf_event_load_external);
  hero_perf_reset(hero_perf_event_store_external);

  // Start counters, do four reads and six writes, and stop counters.
  hero_perf_continue(hero_perf_event_load_external);
  hero_perf_continue(hero_perf_event_store_external);
  const uint32_t foo = *l2;
  const uint32_t bar = *dram;
  const uint32_t bugu = *dram;
  const uint32_t bla = *l2;
  *l2 = 123;
  *dram = 6789;
  *l2 = 9076;
  *l2 = 321;
  *dram = 9876;
  *l2 = 6709;
  hero_perf_pause(hero_perf_event_load_external);
  hero_perf_pause(hero_perf_event_store_external);

  // Do more reads and writes, which must not be counted.
  const uint32_t sam = *dram;
  const uint32_t ba = *l2;
  *dram = 3014;
  *l2 = 8606;

  // Read counters.
  const uint32_t load_external = hero_perf_read(hero_perf_event_load_external);
  const uint32_t store_external = hero_perf_read(hero_perf_event_store_external);

  // Evaluate result.
  unsigned n_errors = 0;
  n_errors += condition_or_printf(load_external == 4,
      "hero_perf_event_load_external was %d instead of 4", load_external);
  n_errors += condition_or_printf(store_external == 6,
      "hero_perf_event_store_external was %d instead of 6", store_external);

  return n_errors;
}

unsigned test_perf(void)
{

  if (hero_rt_core_id() != 0) {
    return 0;
  }

  unsigned n_errors = 0;

  n_errors += local_accesses();
  n_errors += external_accesses();

  return n_errors;
}
