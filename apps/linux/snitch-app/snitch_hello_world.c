#include "printf.h"
#include "snrt.h"
#include <string.h>

// #include "../include/snitch_common.h"
#include "snitch_hero_support.h"

/***********************************************************************************
 * DECLARATIONS
 ***********************************************************************************/
static void a2b_test(char *buf);

/***********************************************************************************
 * DATA
 ***********************************************************************************/
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

  // DMA core sets up the mailboxes and wakes up the others
  if(core_idx == 0) {
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
    printf("Hello from snitch hartid %d (cluster %u, idx %u/%u, is_dma = %i)\n", snrt_hartid(), cluster_idx, core_idx, core_num-1, snrt_is_dm_core());
    printf("Let's wake up the others : (");
    for (unsigned i = 0; i < core_num; i++) {
      if (i == core_idx)
        continue;
      printf("%u ", i);
      snrt_int_sw_set(snrt_global_core_base_hartid() + i);
    }
    printf(")\n");
    snrt_mutex_release(&print_lock);
  }

  snrt_cluster_hw_barrier();

  snrt_mutex_lock(&print_lock);
  printf("Hello again from snitch hartid %d (cluster %u, idx %u/%u, is_dma = %i)\n", snrt_hartid(), cluster_idx, core_idx, core_num-1, snrt_is_dm_core());
  snrt_mutex_release(&print_lock);

  while(1) {;}

  // Signal exit
  syscall(SYS_exit, 0, 0, 0, 0, 0);

  return 0;
}

/***********************************************************************************
 * STATICS
 ***********************************************************************************/
static void a2b_test(char *buf) {
  uint32_t prev_head = 0, ret;
  char c = 'a';
  for (unsigned i = 0; i < 26; i++) {
    printf("abcdefghijklmnopqrstuvwxyz\n");
    if (((prev_head + (26 + 1)) % g_a2h_rb->size) != g_a2h_rb->head) {
      sprintf(buf, "%3d %3d %3d %3d", prev_head, g_a2h_rb->head, g_a2h_rb->size, ret);
      buf += 0x10;
    }
    prev_head = g_a2h_rb->head;
  }
}
