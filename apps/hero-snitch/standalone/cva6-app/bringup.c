
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>

#include "common.h"
#include "fesrv.h"
#include "libsnitch.h"
#include "snitch_common.h"

#define DFLT_CLUSTER_IDX 0

#define max(a, b)           \
  ({                        \
    __typeof__(a) _a = (a); \
    __typeof__(b) _b = (b); \
    _a > _b ? _a : _b;      \
  })
#define min(a, b)           \
  ({                        \
    __typeof__(a) _a = (a); \
    __typeof__(b) _b = (b); \
    _a < _b ? _a : _b;      \
  })

#define ALIGN_UP(x, p) (((x) + (p)-1) & ~((p)-1))

int isolate_all(snitch_dev_t **clusters, uint32_t nr_dev, uint32_t iso) {
  int ret = 0;
  int status;
  for (uint32_t i = 0; i < nr_dev; ++i) {
    status = snitch_isolate(clusters[i], iso);
    if (status != 0) {
      printf("%sisolation failed for cluster %d: %s\n", iso == 0 ? "de-" : "", i, strerror(ret));
      ret -= 1;
    }
  }
  return ret;
}

void set_direct_tlb_map(snitch_dev_t *snitch, uint32_t idx, uint32_t low, uint32_t high) {
  struct axi_tlb_entry tlb_entry;
  tlb_entry.loc = AXI_TLB_NARROW;
  tlb_entry.flags = AXI_TLB_VALID;
  tlb_entry.idx = idx;
  tlb_entry.first = low;
  tlb_entry.last = high;
  tlb_entry.base = low;
  if (snitch_tlb_write(snitch, &tlb_entry)) printf("Wrong tlb write");
  tlb_entry.loc = AXI_TLB_WIDE;
  if (snitch_tlb_write(snitch, &tlb_entry)) printf("Wrong tlb write");
}

void reset_tlbs(snitch_dev_t *snitch) {
  struct axi_tlb_entry tlb_entry;
  tlb_entry.flags = 0;
  tlb_entry.first = 0;
  tlb_entry.last = 0;
  tlb_entry.base = 0;
  for (unsigned idx = 0; idx < 32; ++idx) {
    tlb_entry.idx = idx;
    tlb_entry.loc = AXI_TLB_NARROW;
    snitch_tlb_write(snitch, &tlb_entry);
    tlb_entry.loc = AXI_TLB_WIDE;
    snitch_tlb_write(snitch, &tlb_entry);
  }
}

int main(int argc, char *argv[]) {
  snitch_dev_t *snitch;
  snitch_dev_t **clusters;
  // snitch_perf_t perf;
  void *shared_l3_v;
  int size;
  uint32_t cluster_idx, nr_dev, wake_up_core = 0;
  void *addr, *a2h_rb_addr;
  int ret;
  uint32_t mask;
  struct axi_tlb_entry tlb_entry;

  printf("This is %s\n", argv[0]);
  printf("Usage: %s [snitch_binary [cluster_idx]]\n", argv[0]);
  printf("  Default cluster index is %d\n", DFLT_CLUSTER_IDX);
  fflush(stdout);
  cluster_idx = DFLT_CLUSTER_IDX;
  if (argc == 3) {
    cluster_idx = atoi(argv[2]);
    printf("Running on cluster %d\n", cluster_idx);
  }
  if (argc == 4) {
    wake_up_core = atoi(argv[3]);
    printf("Wake up core = %d\n", wake_up_core);
  }

  // No app specified discover and exit
  snitch_set_log_level(LOG_INFO);
  fflush(stdout);
  if (argc < 2) {
    snitch_discover(NULL, NULL, NULL);
    exit(0);
  }

  // Map clusters to user-space and pick one for tests
  snitch_set_log_level(LOG_MAX);
  clusters = snitch_mmap_all(&nr_dev);
  // Restrict to local cluster and remote on qc
  nr_dev = 1;
  printf("clusters : %lx\n", (uint64_t)&clusters);
  snitch = clusters[cluster_idx];

  // Use L3 layout struct from the cluster provided as argument and set it's pointer in scratch[2]
  ret = snitch_scratch_reg_write(snitch, 2, (uint32_t)(uintptr_t)snitch->l3l_p);

  snitch_test_read_regions(snitch, 0);

  // clear all interrupts
  snitch_ipi_clear(snitch, 0, ~0U);

  // Add TLB entry for required ranges
  // reset_tlbs(snitch);
  set_direct_tlb_map(snitch, 0, 0x01000000, 0x0101ffff);  // BOOTROM
  set_direct_tlb_map(snitch, 1, 0x02000000, 0x02000fff);  // SoC Control
  set_direct_tlb_map(snitch, 2, 0x04000000, 0x040fffff);  // CLINT
  set_direct_tlb_map(snitch, 3, 0x10000000, 0x105fffff);  // Quadrants
  set_direct_tlb_map(snitch, 4, 0x80000000, 0xffffffff);  // HBM0/1

  for (unsigned i = 0; i < 5; ++i) {
    memset(&tlb_entry, 0, sizeof(tlb_entry));
    tlb_entry.loc = AXI_TLB_WIDE;
    tlb_entry.idx = i;
    snitch_tlb_read(snitch, &tlb_entry);
    printf("TLB readback Wide: idx %ld first %012lx last %012lx base %012lx flags %02x\n",
           tlb_entry.idx, tlb_entry.first, tlb_entry.last, tlb_entry.base, tlb_entry.flags);
    fflush(stdout);
    memset(&tlb_entry, 0, sizeof(tlb_entry));
    tlb_entry.loc = AXI_TLB_NARROW;
    tlb_entry.idx = i;
    snitch_tlb_read(snitch, &tlb_entry);
    printf("TLB readback Narrow: idx %ld first %012lx last %012lx base %012lx flags %02x\n",
           tlb_entry.idx, tlb_entry.first, tlb_entry.last, tlb_entry.base, tlb_entry.flags);
    fflush(stdout);
  }

  // De-isolate quadrant
  isolate_all(clusters, nr_dev, 1);
  ret = isolate_all(clusters, nr_dev, 0);
  if (ret) {
    isolate_all(clusters, nr_dev, 1);
    exit(-1);
  }

  // setup front-end server. Do this here so that the host communication data is before any other
  // data in L3 to prevent overwriting thereof
  fesrv_t *fs = malloc(sizeof(fesrv_t));
  fesrv_init(fs, snitch, &a2h_rb_addr);
  snitch->l3l->a2h_rb = (uint32_t)(uintptr_t)a2h_rb_addr;

  // fill memory with known pattern
  if (memtest(snitch->l1.v_addr, snitch->l1.size, "TCDM", 'T')) return -1;

  // and some test scratch l3 memory
  // For largest axpy problem: (2*N+1)*sizeof(double), N=3*3*6*2048
  // For largest conv2d problem: (64*112*112+64*64*7*7+64*112*112)*sizeof(double) = 14112*1024
  // 2x for good measure
  shared_l3_v = snitch_l3_malloc(snitch, 2 * 14112 * 1024, &addr);
  assert(shared_l3_v);
  snitch->l3l->heap = (uint32_t)(uintptr_t)addr;
  printf("alloc l3l_v->heap: %08x\r\n", snitch->l3l->heap);
  if (memtest(shared_l3_v, 1024, "L3", '3')) return -1;

  snprintf(shared_l3_v, 1024, "this is linux");
  fflush(stdout);

  /* READ IMAGE START */
  FILE *fp = fopen("/root/test_img.png", "rb");
  if (!fp) {
    perror("fopen");
    return EXIT_FAILURE;
  }

#define ARRAY_SIZE(arr) (sizeof(arr) / sizeof((arr)[0]))

  unsigned char buffer[8];

  unsigned int offload_ptr = 0;

  while (!feof(fp)) {
    for (unsigned int i = 0; i < fread(buffer, sizeof(*buffer), ARRAY_SIZE(buffer), fp); i++) {
      ((char *)shared_l3_v)[offload_ptr] = buffer[offload_ptr%8];
      offload_ptr += 1;
    }
  }

  printf("---> PNG magic: %#04x%02x%02x%02x\n", ((char *)shared_l3_v)[0], ((char *)shared_l3_v)[1], ((char *)shared_l3_v)[2], ((char *)shared_l3_v)[3]);
  printf("---> Bytes read : %u\n", offload_ptr);

  /* READ IMAGE ENDS */

  if (argc >= 2) {
    size = snitch_load_bin(snitch, argv[1]);
    if (size < 0) goto exit;

    printf("Data in allocated L3:\n");
    hexdump((void *)shared_l3_v, 32);
    printf("Data in L1:\n");
    hexdump(snitch->l1.v_addr, 32);
    fflush(stdout);

    // Fill some stuff in the mailbox
    snitch_mbox_write(snitch, 100);
    snitch_mbox_write(snitch, 101);
    snitch_mbox_write(snitch, 102);

    printf("Set interrupt on core %u\n", wake_up_core);
    snitch_ipi_set(snitch, 0, 1 << (wake_up_core + cluster_idx * 9 + 1));
    // snitch_ipi_set(snitch, 0, 0x3FE);
    fflush(stdout);

    printf("Waiting for program to terminate..\n");
    fflush(stdout);
    fs->abortAfter = 30;
    fesrv_run(fs);
    // sleep(3);

    printf("Data in allocated L3:\n");
    hexdump((void *)shared_l3_v, 32);
    printf("Data in L1:\n");
    hexdump(snitch->l1.v_addr, 6 * 0x10);

    // read mailbox
    uint32_t msg;
    while (snitch_mbox_try_read(snitch, &msg)) {
      printf("Mailbox: %d\n", msg);
    }

    snitch_ipi_get(snitch, 0, &mask);
    printf("clint after completion: %08x\n", mask);
  }

exit:
  snitch_ipi_clear(snitch, 0, ~0U);
  ret = isolate_all(clusters, nr_dev, 1);

  printf("Exiting\n");
  return ret;
}
