#include <string.h>

#include "printf.h"
#include "snrt.h"

// #include "../include/snitch_common.h"
#include "snitch_hero_support.h"

/***********************************************************************************
 * DATA
 ***********************************************************************************/

extern const uint32_t scratch_reg;  // In start_snitch.S
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
  if (snrt_is_dm_core()) {
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

    snrt_mutex_lock(&print_lock);
    printf("(cluster %u, idx %u/%u, is_dma = %i) Finished setting up mailboxes\n", cluster_idx,
           core_idx, core_num - 1, snrt_is_dm_core());
    snrt_mutex_release(&print_lock);
  }

  snrt_cluster_hw_barrier();

  snrt_mutex_lock(&print_lock);
  printf("Hello from snitch hartid %d (cluster %u, idx %u/%u, is_dma = %i)\n", snrt_hartid(),
         cluster_idx, core_idx, core_num - 1, snrt_is_dm_core());
  snrt_mutex_release(&print_lock);

  if (core_idx == 2) {
    snrt_mutex_lock(&print_lock);
    printf("(cluster %u, idx %u/%u, is_dma = %i) ---> PNG magic: %#04x%02x%02x%02x\n", cluster_idx,
           core_idx, core_num - 1, snrt_is_dm_core(), l3[0], l3[1], l3[2], l3[3]);
    printf("%u %u %u %u\n", l3[152], l3[153], l3[154], l3[155]);
    snrt_mutex_release(&print_lock);
  }

  snrt_cluster_hw_barrier();

  if (!snrt_is_dm_core()) {
    // Now everything is initialized....
    uint16_t act_hex = 0x000094a2;
    uint16_t img_hex = 0x00002905;
    uint16_t weight_hex = 0x0000275f;
    __fp16 act = *((__fp16 volatile *)&act_hex);
    __fp16 img = *((__fp16 volatile *)&img_hex);
    __fp16 weight = *((__fp16 volatile *)&weight_hex);
    __fp16 volatile mac_trigger;
    mac_trigger = act + img * weight;
    snrt_mutex_lock(&print_lock);
    printf("(cluster %u, idx %u/%u, is_dma = %i) MAC trigger: %f\n", cluster_idx, core_idx,
           core_num - 1, snrt_is_dm_core(), mac_trigger);
    snrt_mutex_release(&print_lock);
  }

  snrt_cluster_hw_barrier();

  // Signal exit
  syscall(SYS_exit, 0, 0, 0, 0, 0);

  return 0;
}
