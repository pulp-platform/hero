#include "printf.h"
#include "snrt.h"
#include <string.h>

// #include "../include/snitch_common.h"
#include "snitch_hero_support.h"

/***********************************************************************************
 * DATA
 ***********************************************************************************/

extern const uint32_t scratch_reg; // In start_snitch.S
static volatile uint32_t *const soc_scratch0 = (uint32_t *)(0x02000014);
static volatile uint32_t *soc_scratch = soc_scratch0;
extern volatile struct ring_buf *g_a2h_rb;
extern volatile struct ring_buf *g_a2h_mbox;
extern volatile struct ring_buf *g_h2a_mbox;
static volatile int32_t print_lock;
static volatile uint8_t *l3;

/***********************************************************************************
 * MAIN
 ***********************************************************************************/

int main(void) {

  struct l3_layout l3l;
  int ret;
  volatile struct ring_buf priv_rb;

  unsigned cluster_idx = snrt_cluster_idx();
  unsigned core_idx = snrt_global_core_idx();
  unsigned core_num = snrt_global_core_num();

  // First core sets up the mailboxes and stuff
  if(snrt_is_dm_core()) {
    // Read memory layout from scratch2 (L3)
    memcpy(&l3l, (void *)soc_scratch[2], sizeof(struct l3_layout));
    // Setup mailboxes (in L3)
    g_a2h_rb = (struct ring_buf *)l3l.a2h_rb;
    g_a2h_mbox = (struct ring_buf *)l3l.a2h_mbox;
    g_h2a_mbox = (struct ring_buf *)l3l.h2a_mbox;
    // Setup shared heap (in L3)
    l3 = (uint8_t *)l3l.heap;
    // Setup print lock
    print_lock = 0;
  }

  snrt_cluster_hw_barrier();

  snrt_mutex_lock(&print_lock);
  printf("Hello from snitch hartid %d (cluster %u, idx %u/%u, is_dma = %i)\n", snrt_hartid(), cluster_idx, core_idx, core_num-1, snrt_is_dm_core());
  snrt_mutex_release(&print_lock);

  // Signal exit
  syscall(SYS_exit, 0, 0, 0, 0, 0);

  return 0;
}
