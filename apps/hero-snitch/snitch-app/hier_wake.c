
#include <snrt.h>
#include <stdint.h>

/**
 * @brief Called by each hart before the pre-main barrier in snrt crt0
 *
 */
void _snrt_hier_wakeup(void) {
  const uint32_t core_id = snrt_cluster_core_idx();

  // master core wakes other cluster cores through cluster local clint
  if (core_id == 0) {
    // clear the interrupt from cva6
    snrt_int_sw_clear(snrt_hartid());
    // wake remaining cluster cores
    const unsigned cluster_core_num = snrt_cluster_core_num();
    snrt_int_cluster_set(~0x1 & ((1 << cluster_core_num) - 1));
  } else {
    // clear my interrupt
    snrt_int_cluster_clr(1 << core_id);
  }
}

void snrt_hier_wakeup_wake(uint32_t phys_cluster_num, uint32_t mst_cluster) {
  if (snrt_is_dm_core() && snrt_cluster_idx() == mst_cluster) {
    for (unsigned cl = 0; cl < phys_cluster_num; ++cl)
      if (cl != snrt_cluster_idx())
        snrt_int_sw_set(1 + cl * 9);
  }
}
