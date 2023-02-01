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

#define FILE_SIZE 128
uint8_t file_content[FILE_SIZE];

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
  printf("(cluster %u, idx %u/%u, is_dma = %i) Hello from snitch hartid %d\n", cluster_idx,
         core_idx, core_num - 1, snrt_is_dm_core(), snrt_hartid());
  snrt_mutex_release(&print_lock);

  snrt_cluster_hw_barrier();

  // From now on every thing is initialized

  /* Get file */

  if (snrt_is_dm_core()) {
    snrt_mutex_lock(&print_lock);
    printf("\n(cluster %u, idx %u/%u, is_dma = %i) Reading data from L3:", cluster_idx, core_idx,
           core_num - 1, snrt_is_dm_core());
    for (unsigned int i = 0; i < FILE_SIZE; i++) {
      file_content[i] = l3[i];
      if (i % 16 == 0) printf("\n%#x -> %#x -- ", &l3[i], &file_content[i]);
      printf("%x ", file_content[i]);
    }
    printf("\n");
    snrt_mutex_release(&print_lock);
  }

  snrt_cluster_hw_barrier();

  /* Print file */
  if (core_idx == 2) {
    snrt_mutex_lock(&print_lock);
    printf("(cluster %u, idx %u/%u, is_dma = %i) Printing data from L2:\n %s\n", cluster_idx, core_idx, core_num - 1,
           snrt_is_dm_core(), file_content);
    snrt_mutex_release(&print_lock);
  }

  snrt_cluster_hw_barrier();

  /* Print FP test */
  if (!snrt_is_dm_core()) {
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

  /* Barrier before exiting */
  snrt_cluster_hw_barrier();

  // Signal exit
  syscall(SYS_exit, 0, 0, 0, 0, 0);

  return 0;
}
