/*
 * @Author: Noah Huetter
 * @Date:   2020-10-02 10:58:48
 * @Last Modified by:   Noah Huetter
 * @Last Modified time: 2020-11-09 17:09:55
 */
#include "libsnitch.h"
#include "snitch_common.h"

#include "debug.h"
#include "fesrv.h"
#include "o1heap.h"
#include "herodev.h"

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <glob.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <time.h>
#include <unistd.h>

// ----------------------------------------------------------------------------
//
//   Macros
//
// ----------------------------------------------------------------------------

#define ALIGN_UP(x, p) (((x) + (p)-1) & ~((p)-1))

enum log_level g_debuglevel = LOG_ERROR;
enum log_level g_snitch_debuglevel = LOG_ERROR;

// ----------------------------------------------------------------------------
//
//   Type declarations
//
// ----------------------------------------------------------------------------

// ----------------------------------------------------------------------------
//
//   Static prototypes
//
// ----------------------------------------------------------------------------
static void populate_boot_data(snitch_dev_t *dev, struct BootData *bd);

// ----------------------------------------------------------------------------
//
//   Static Data
//
// ----------------------------------------------------------------------------

// Need to share L3 resources accross clusters. They are mapped by the first mmap
// and then copied to to individual snitch devices (this is ugly but ok for now)
// Should be protected by a mutex and also, the properties are taken from the first
// cluster (as per design these are shared resources)
// TODO: Make not ugly
static SnitchSubDev *g_l3 = NULL;
struct O1HeapInstance *g_l3_heap_mgr = NULL;
uint64_t g_l3_data_offset = 0;

// ----------------------------------------------------------------------------
//
//   Public functions
//
// ----------------------------------------------------------------------------

void snitch_set_log_level(enum log_level ll) { g_debuglevel = ll; }

int snitch_discover(char ***devs, uint32_t *clusters, uint32_t *quadrants) {
  int ret;
  glob_t globbuf;
  char **fname;
  int fd;
  ssize_t size;
  struct sn_cluster_info sci;
  uint32_t cores = 0, dm_cores = 0, l_clusters, l_quadrants;
  uint8_t quadrant_present[256];
  ret = glob("/dev/snitch*", GLOB_ERR, NULL, &globbuf);
  glob("../*.c", GLOB_DOOFFS | GLOB_APPEND, NULL, &globbuf);

  l_clusters = 0;
  l_quadrants = 0;
  memset(quadrant_present, 0, sizeof(quadrant_present));

  if (ret) {
    if (ret == GLOB_NOMATCH)
      pr_info("No matches\n");
    else
      pr_trace("glob error: %s\n", strerror(errno));
    return -errno;
  }
  pr_info("Found %zu chardev matches\n", globbuf.gl_pathc);
  fname = globbuf.gl_pathv;

  if (devs)
    *devs = malloc(globbuf.gl_pathc * sizeof(char *));

  ret = 0;
  while (*fname) {
    // open device
    fd = open(*fname, O_RDWR | O_SYNC);
    if (fd < 0) {
      pr_error("Opening failed. %s \n", strerror(errno));
      goto skip;
    }

    // try reading snitch cluster struct
    size = read(fd, &sci, sizeof(sci));
    if (size != sizeof(sci)) {
      pr_error("Reading snitch cluster info failed\n");
      goto skip;
    }
    pr_info(" quadrant: %d cluster: %d computer-cores: %d dm-cores: %d l1: %ldKiB l3: %ldKiB\n",
            sci.quadrant_idx, sci.cluster_idx, sci.compute_num, sci.dm_num, sci.l1_size / 1024,
            sci.l3_size / 1024);

    if (devs)
      (*devs)[ret] = strdup(*fname);

    cores += sci.compute_num + sci.dm_num;
    dm_cores += sci.dm_num;
    // count number of quadrants
    if (sci.quadrant_idx < sizeof(quadrant_present) && !quadrant_present[sci.quadrant_idx]) {
      ++l_quadrants;
      quadrant_present[sci.quadrant_idx] = 1;
    } else if (sci.quadrant_idx > sizeof(quadrant_present)) {
      pr_error("Array overflow!\n");
    }
    ++l_clusters;

    ++ret;
  skip:
    close(fd);
    ++fname;
  }

  pr_info("Successfully probed %u clusters and found a total of %d (%d compute, %d dm) cores!\n",
          ret, cores, cores - dm_cores, dm_cores);

  if (clusters)
    *clusters = l_clusters;
  if (quadrants)
    *quadrants = l_quadrants;

  return ret;
}

snitch_dev_t **snitch_mmap_all(uint32_t *nr_dev) {
  int ret, ndev;
  char **dev_names;
  snitch_dev_t **devs;
  uint32_t quadrants, clusters;

  ndev = snitch_discover(&dev_names, &clusters, &quadrants);
  if (ndev < 0) {
    *nr_dev = ndev;
    return NULL;
  }

  devs = malloc(ndev * sizeof(snitch_dev_t *));

  for (unsigned i = 0; i < ndev; ++i) {
    pr_info("Mapping dev: %s\n", dev_names[i]);
    devs[i] = malloc(sizeof(snitch_dev_t));
    ret = snitch_mmap(devs[i], dev_names[i]);

    if (ret < 0)
      goto fail;
  }
  *nr_dev = ndev;
  return devs;
fail:
  *nr_dev = ret;
  free(devs);
  return NULL;
}

int snitch_mmap(snitch_dev_t *dev, char *fname) {
  // int offset;
  ssize_t size;
  void *addr, *addr2;

  // This is probably the first call into this library, set the debug level from ENV here
  const char *s = getenv("LIBSNITCH_DEBUG");
  if (s != NULL) {
    g_debuglevel = atoi(s);
    pr_trace("Set debug level to %d\n", g_debuglevel);
  }

  pr_trace("mmap with %s\n", fname);

  // open device
  dev->fd = open(fname, O_RDWR | O_SYNC);
  if (dev->fd < 0) {
    pr_error("Opening failed. %s \n", strerror(errno));
    return -ENOENT;
  }

  // try reading snitch cluster struct
  size = read(dev->fd, &dev->sci, sizeof(dev->sci));
  if (size != sizeof(dev->sci)) {
    pr_error("Reading snitch cluster info failed\n");
    goto close;
  }
  pr_info("computer-cores: %d dm-cores: %d l1: %08lx %ldKiB l3: %08lx %ldKiB clint: %08lx\n",
          dev->sci.compute_num, dev->sci.dm_num, dev->sci.l1_paddr, dev->sci.l1_size / 1024, dev->sci.l3_paddr, dev->sci.l3_size / 1024,
          dev->sci.clint_base);

  // mmap tcdm
  dev->l1.size = dev->sci.l1_size;
  dev->l1.p_addr = dev->sci.l1_paddr;
  dev->l1.v_addr =
      mmap(NULL, dev->l1.size, PROT_READ | PROT_WRITE, MAP_SHARED, dev->fd, SNITCH_MMAP_TCDM);
  if (dev->l1.v_addr == MAP_FAILED) {
    pr_error("mmap() failed for TCDM. %s\n", strerror(errno));
    // return -EIO;
  }
  pr_debug("TCDM mapped to virtual user space at %p.\n", dev->l1.v_addr);

  // mmap reserved DDR space
  if (!g_l3) {
    g_l3 = malloc(sizeof(*g_l3));
    g_l3->size = dev->sci.l3_size;
    g_l3->p_addr = dev->sci.l3_paddr;
    g_l3->v_addr =
        mmap(NULL, g_l3->size, PROT_READ | PROT_WRITE, MAP_SHARED, dev->fd, SNITCH_MMAP_L3);
    if (g_l3->v_addr == MAP_FAILED) {
      pr_error("mmap() failed for Shared L3 memory. %s\n", strerror(errno));
      // return -EIO;
    }
    pr_debug("Shared L3 memory mapped to virtual user space at %p.\n", g_l3->v_addr);
  }
  memcpy(&dev->l3, g_l3, sizeof(*g_l3));

  // Initialize L3 heap manager in the middle of the reserved memory range
  if (!g_l3_heap_mgr) {
    g_l3_data_offset = ALIGN_UP(dev->l3.size / 2, O1HEAP_ALIGNMENT);
    pr_debug("Initializing o1heap at %p size %x\n", (void *)(dev->l3.v_addr + g_l3_data_offset),
             dev->l3.size / 2);
    g_l3_heap_mgr =
        o1heapInit((void *)(dev->l3.v_addr + g_l3_data_offset), dev->l3.size / 2, NULL, NULL);
    if (g_l3_heap_mgr == NULL) {
      pr_error("Failed to initialize L3 heap manager.\n");
      return -ENOMEM;
    } else {
      pr_debug("Allocated L3 heap manager at %p.\n", g_l3_heap_mgr);
    }
  }
  dev->l3_heap_mgr = g_l3_heap_mgr;
  dev->l3_data_offset = g_l3_data_offset;

  // Put a l3 layout struct into shared L3 to pass initial pointers to snitch
  // Pointer to this struct passed to snitch through scratch 2 register
  dev->l3l = snitch_l3_malloc(dev, sizeof(struct l3_layout), &dev->l3l_p);
  assert(dev->l3l);

  // Mailboxes a2h and h2a of 16*uint32_t each
  dev->a2h_mbox = (struct ring_buf *)snitch_l3_malloc(dev, sizeof(struct ring_buf), &addr);
  assert(dev->a2h_mbox);
  dev->l3l->a2h_mbox = (uint32_t)(uintptr_t)addr;
  dev->a2h_mbox->data_v = (uint64_t)snitch_l3_malloc(dev, sizeof(uint32_t) * 16, &addr2);
  assert(dev->a2h_mbox->data_v);
  dev->a2h_mbox->data_p = (uint64_t)addr2;
  rb_init(dev->a2h_mbox, 16, sizeof(uint32_t));
  pr_debug("a2h mailbox at phys %08x data %08lx\n", dev->l3l->a2h_mbox, dev->a2h_mbox->data_p);
  // Mailboxes a2h and h2a of 16*uint32_t each
  dev->h2a_mbox = (struct ring_buf *)snitch_l3_malloc(dev, sizeof(struct ring_buf), &addr);
  assert(dev->h2a_mbox);
  dev->l3l->h2a_mbox = (uint32_t)(uintptr_t)addr;
  dev->h2a_mbox->data_v = (uint64_t)snitch_l3_malloc(dev, sizeof(uint32_t) * 16, &addr2);
  assert(dev->h2a_mbox->data_v);
  dev->h2a_mbox->data_p = (uint64_t)addr2;
  rb_init(dev->h2a_mbox, 16, sizeof(uint32_t));
  pr_debug("h2a mailbox at phys %08x data %08lx\n", dev->l3l->h2a_mbox, dev->h2a_mbox->data_p);

  return 0;

close:
  close(dev->fd);
  return -ENOENT;
}

int snitch_flush(snitch_dev_t *dev) {
  // forward to driver
  return ioctl(dev->fd, SNIOS_FLUSH);
}

int snitch_reset(snitch_dev_t *dev) {
  int ret;

  // Put clusters in isolation
  ret = snitch_isolate(dev, 1);
  if (ret)
    return ret;

  // de-isolate
  ret = snitch_isolate(dev, 0);
  if (ret)
    return ret;

  return 0;
}

int snitch_load_bin(snitch_dev_t *dev, const char *name) {
  FILE *fd;
  size_t size;
  int ret;
  uint8_t *dat;
  unsigned errs = 0;
  uint32_t boot_data_off;
  struct BootData *bd;

  ret = access(name, R_OK);
  if (ret) {
    pr_error("Can't access file %s: %s\n", name, strerror(ret));
    return ret;
  }

  fd = fopen(name, "rb");
  if (!fd) {
    pr_error("File %s open failed: %s\n", name, strerror(errno));
    return errno;
  }

  // get file size and check if it fits L3
  fseek(fd, 0L, SEEK_END);
  size = ftell(fd);
  fseek(fd, 0L, SEEK_SET);
  if (size > dev->l3.size) {
    pr_error("binary exceeds L3 size: %ld > %d\n", size, dev->l3.size);
    ret = -EFBIG;
    goto abort;
  }

  pr_trace("copy binary %s to L3\n", name);
  fread(dev->l3.v_addr, size, 1, fd);
  snitch_flush(dev);

  // testing: read file to memory and compare with L3
  dat = (uint8_t *)malloc(size);
  fseek(fd, 0L, SEEK_SET);
  fread(dat, size, 1, fd);
  for (unsigned i = 0; errs < 8 && i < size; ++i)
    errs = ((uint8_t *)dev->l3.v_addr)[i] != dat[i] ? errs + 1 : errs;
  pr_trace("Verify accelerator binary in L3: %s %d errors (of %ld bytes)\n",
           errs != 0 ? SHELL_RED "FAIL" SHELL_RST : SHELL_GRN "PASS" SHELL_RST, errs, size);
  free(dat);
  if (errs) {
    pr_error("Verify failed\n");
    ret = -EIO;
    goto abort;
  } else {
    ret = size;
  }

  // Set entry-point
  snitch_scratch_reg_write(dev, 0, (uint64_t)dev->l3.p_addr);

  // Program boot-rom and set pointer to it in scratch1
  boot_data_off = ALIGN_UP(size, 0x100);
  pr_trace("copy bootrom data to L3 and setting pointer in scratch1\n");
  snitch_scratch_reg_write(dev, 1, (uint64_t)dev->l3.p_addr + boot_data_off);
  bd = malloc(sizeof(*bd));
  if (!bd) {
    pr_error("error allocating boot data: %s\n", strerror(errno));
    ret = -ENOMEM;
    goto abort;
  }
  populate_boot_data(dev, bd);

  memcpy((uint8_t *)dev->l3.v_addr + boot_data_off, bd, sizeof(*bd));
  free(bd);

abort:
  fclose(fd);
  return ret;
}

int snitch_isolate(snitch_dev_t *dev, int iso) {
  // Forward to the driver
  uint32_t cmd;
  int ret;
  if (iso)
    cmd = SNIOS_ISOLATE;
  else
    cmd = SNIOS_DEISOLATE;
  if ((ret = ioctl(dev->fd, SNIOC_SET_OPTIONS, &cmd))) {
    pr_error("ioctl() failed. %s \n", strerror(errno));
  } else {
    pr_debug("%sisolate success on quadrant %d\n", iso ? "" : "de", dev->sci.quadrant_idx);
  }
  return ret;
}

int snitch_scratch_reg_write(snitch_dev_t *dev, uint32_t reg, uint32_t val) {
  int ret;
  struct snios_reg sreg;
  sreg.off = reg;
  sreg.val = val;
  if ((ret = ioctl(dev->fd, SNIOS_SCRATCH_W, &sreg))) {
    pr_error("ioctl() failed. %s \n", strerror(errno));
  }
  return ret;
}

int snitch_scratch_reg_read(snitch_dev_t *dev, uint32_t reg, uint32_t *val) {
  int ret;
  struct snios_reg sreg;
  sreg.off = reg;
  if ((ret = ioctl(dev->fd, SNIOS_SCRATCH_R, &sreg))) {
    pr_error("ioctl() failed. %s \n", strerror(errno));
  }
  return ret;
}

int snitch_ipi_set(snitch_dev_t *dev, uint32_t reg, uint32_t mask) {
  int ret;
  struct snios_reg sreg;
  sreg.off = reg;
  sreg.val = mask;
  if ((ret = ioctl(dev->fd, SNIOS_SET_IPI, &sreg))) {
    pr_error("ioctl() failed. %s \n", strerror(errno));
  }
  return ret;
}

int snitch_ipi_clear(snitch_dev_t *dev, uint32_t reg, uint32_t mask) {
  int ret;
  struct snios_reg sreg;
  sreg.off = reg;
  sreg.val = mask;
  if ((ret = ioctl(dev->fd, SNIOS_CLEAR_IPI, &sreg))) {
    pr_error("ioctl() failed. %s \n", strerror(errno));
  }
  return ret;
}

int snitch_tlb_write(snitch_dev_t *dev, struct axi_tlb_entry *e) {
  int ret;

  pr_trace("TLB write slice: loc %s idx %ld first %012lx last %012lx base %012lx flags %02x\n",
           e->loc == AXI_TLB_NARROW ? "narrow" : "wide", e->idx, e->first, e->last, e->base,
           e->flags);

  if ((ret = ioctl(dev->fd, SNIOS_WRITE_TLB_ENTRY, e))) {
    pr_error("ioctl() failed. %s \n", strerror(errno));
  }
  return ret;
}

int snitch_tlb_read(snitch_dev_t *dev, struct axi_tlb_entry *e) {
  int ret;
  if ((ret = ioctl(dev->fd, SNIOS_READ_TLB_ENTRY, e))) {
    pr_error("ioctl() failed. %s \n", strerror(errno));
  }
  return ret;
}

int snitch_ipi_get(snitch_dev_t *dev, uint32_t reg, uint32_t *mask) {
  int ret;
  struct snios_reg sreg;
  sreg.off = reg;
  if ((ret = ioctl(dev->fd, SNIOS_GET_IPI, &sreg))) {
    pr_error("ioctl() failed. %s \n", strerror(errno));
  }
  *mask = sreg.val;
  return ret;
}


void snitch_fesrv_run(snitch_dev_t *dev) {
  pr_error("unimplemented\n");
  // // init fesrv
  // dev->fesrv.hsmem = dev->bram.v_addr;
  // dev->fesrv.dmem = dev->l1.v_addr;
  // fesrvInit(&dev->fesrv, SNITCH_TOT_NR_CORES);
  // dev->fesrv.dataOffset = 0;
  // dev->fesrv.dmemSize = H_l1_SIZE_B;
  // // do not autoabort
  // dev->fesrv.runFor = 0;

  // // call polling thread
  // fesrvRun(&dev->fesrv);
}

int snitch_read_performance(snitch_dev_t *dev, snitch_perf_t *perf) {
  pr_error("unimplemented\n");
  return -1;
  // perf->counters = malloc(SNITCH_PERIPH_PERF_CNT_PER_CORE * SNITCH_TOT_NR_CORES *
  // sizeof(uint32_t));

  // if (!perf->counters) {
  //   printf("Memory allocation failed\n");
  //   return -1;
  // }

  // uint64_t *p = (uint64_t *)dev->periph.v_addr;

  // perf->l1StartAddress = p[SNITCH_PERIPH_TCDM_START / 8];
  // perf->l1EndAddress = p[SNITCH_PERIPH_TCDM_END / 8];
  // perf->nrCores = p[SNITCH_PERIPH_NR_CORES / 8];
  // perf->fetchEnable = p[SNITCH_PERIPH_FETCH_ENA / 8];
  // perf->scratch = p[SNITCH_PERIPH_SCRATCH_REG / 8];
  // perf->cycle = p[SNITCH_PERIPH_CYCLE_COUNT / 8];
  // perf->barrier = p[SNITCH_PERIPH_BARRIER / 8];
  // perf->hartBaseID = p[SNITCH_PERIPH_CLUSTER_ID / 8];
  // perf->l1Accessed = p[SNITCH_PERIPH_TCDM_ACCESSED / 8];
  // perf->l1Congested = p[SNITCH_PERIPH_TCDM_CONGESTED / 8];

  // for (int i = 0; i < SNITCH_PERIPH_PERF_CNT_PER_CORE * SNITCH_TOT_NR_CORES; i++)
  //   perf->counters[i] = p[SNITCH_PERIPH_PERF_CNT / 8 + i];

  // return SNITCH_PERIPH_PERF_CNT_PER_CORE * SNITCH_TOT_NR_CORES;
}

void *snitch_l3_malloc(snitch_dev_t *dev, size_t size, void **p_addr) {
  // Align
  if (size & 0x7) {
    size = (size & ~0x7) + 0x8;
  }

  void *v_addr = o1heapAllocate((O1HeapInstance *)dev->l3_heap_mgr, size);
  if (v_addr == 0) {
    return 0;
  }

  // Calculate physical address.
  *p_addr = dev->l3.p_addr + (v_addr - dev->l3.v_addr);
  pr_trace("snitch_l3_malloc: size: %lx virt: %p phys: %p\n", size, v_addr, *p_addr);

  return v_addr;
}

void snitch_l3_free(snitch_dev_t *dev, void *v_addr, void *p_addr) {
  o1heapFree((O1HeapInstance *)dev->l3_heap_mgr, v_addr);
}

int snitch_exec_done(snitch_dev_t *dev, uint64_t *mask) {
  pr_error("unimplemented\n");
  return -1;
  // int ret = 0;
  // uint64_t imask = 0;
  // for (int i = 0; i < dev->fesrv.nrCores; i++) {
  //   ret += (dev->fesrv.coresExited[i] == 1) ? 1 : 0;
  //   imask |= ((dev->fesrv.coresExited[i] == 1) ? 1 : 0) << i;
  // }
  // if (mask)
  //   *mask = imask;
  // return ret;
}

int snitch_exe_wait(snitch_dev_t *dev, uint32_t mask, int timeout_s) {
  pr_error("unimplemented\n");
  return -1;
  // int start = time(NULL);
  // uint64_t imask = 0;
  // unsigned long calls = dev->fesrv.nCalls;
  // do {
  //   (void)snitch_exec_done(dev, &imask);
  //   if (__builtin_popcount(imask & mask) == __builtin_popcount(mask))
  //     return 0;
  //   if (calls < dev->fesrv.nCalls) {
  //     // reset timeout
  //     calls = dev->fesrv.nCalls;
  //     start = time(NULL);
  //   }
  // } while (time(NULL) < (start + timeout_s));
  // return -1;
}

void snitch_dbg_stack(snitch_dev_t *dev, uint32_t stack_size, char fill) {
  pr_error("unimplemented\n");
  // uint32_t stack_base;
  // char *p = (char *)dev->l1.v_addr;
  // char mem;
  // int stack_idx;

  // printf("Stack size per core: %d bytes\n", stack_size);

  // for (int hart_id = 0; hart_id < SNITCH_TOT_NR_CORES; hart_id++) {
  //   // calculate stack pointer base address
  //   stack_base = hart_id * stack_size;
  //   // start at stack end and stop if pattern is not found anymore
  //   for (stack_idx = stack_size - 1; stack_idx != 0; stack_idx--) {
  //     // read memory
  //     mem = p[dev->l1.size - stack_base - stack_idx];
  //     if (mem != fill) {
  //       // this location was used, report and abort
  //       // printf("mismatch at %#x\n", dev->l1.size - stack_base - stack_idx);
  //       break;
  //     }
  //   }
  //   printf("Core %2d stack usage: %6d bytes (%.0f%%)\n", hart_id, stack_idx,
  //          100.0 / stack_size * stack_idx);
  // }
}

int snitch_mbox_read(const snitch_dev_t *dev, uint32_t *buffer, size_t n_words) {
  int ret, retry = 0;
  while (n_words--) {
    do {
      ret = rb_host_get(dev->a2h_mbox, &buffer[n_words]);
      if (ret) {
        if (++retry == 100) {
          pr_warn("high retry on mbox read()\n");
        }
        usleep(10000);
      }
    } while (ret);
  }
  return 0;
}

int snitch_mbox_try_read(const snitch_dev_t *dev, uint32_t *buffer) {
  return rb_host_get(dev->a2h_mbox, buffer) == 0 ? 1 : 0;
}

int snitch_mbox_write(snitch_dev_t *dev, uint32_t word) {
  pr_trace("mbox write %08x\n", word);
  int ret, retry = 0;
  do {
    ret = rb_host_put(dev->h2a_mbox, &word);
    if (ret) {
      if (++retry == 100) {
        pr_warn("high retry on mbox write()\n");
      }
      usleep(10000);
    }
  } while (ret);
  return ret;
}

void snitch_set_device_loglevel(snitch_dev_t *dev, int lvl) {
  // the default
  g_snitch_debuglevel = 0;
  if (lvl == -1) {
    const char *s = getenv("SNITCH_DEBUG");
    if (s != NULL) {
      g_snitch_debuglevel = atoi(s);
    }
  } else {
    g_snitch_debuglevel = lvl;
  }
  pr_trace("Set snitch debug level to %d\n", g_snitch_debuglevel);
  snitch_mbox_write(dev, MBOX_DEVICE_LOGLVL);
  snitch_mbox_write(dev, g_snitch_debuglevel);
}

// ----------------------------------------------------------------------------
//
//   Static
//
// ----------------------------------------------------------------------------

static void populate_boot_data(snitch_dev_t *dev, struct BootData *bd) {
  bd->core_count = dev->sci.compute_num + dev->sci.dm_num;
  // hartid of first snitch core
  bd->hartid_base = 1;
  // Global cluster base address. Each cluster's TCDM is calculated using this offset,
  // tcdm_offset, hartid_base and mhartid CSR
  bd->tcdm_start = 0x10000000;
  // size of TCDM address space
  bd->tcdm_size = 0x20000;
  // offset between cluster address spaces
  bd->tcdm_offset = 0x40000;
  bd->global_mem_start = (uint32_t)(uintptr_t)(dev->sci.l3_paddr + dev->l3_data_offset);
  bd->global_mem_end = (uint32_t)(uintptr_t)(dev->sci.l3_paddr + dev->l3.size);
  // TODO: Handle multi-cluster
  bd->cluster_count = 1;
  // Let's pretend all clusters were in the same quadrant
  bd->s1_quadrant_count = 1;
  bd->clint_base = dev->sci.clint_base;
  // unused
  bd->boot_addr = (uint32_t)(uintptr_t)dev->sci.l3_paddr;
}

int snitch_test_read_regions(snitch_dev_t *dev, uint32_t reg) {
  int ret;
  struct snios_reg sreg;
  sreg.off = reg;
  if ((ret = ioctl(dev->fd, SNIOS_TEST_READ_REGIONS, &sreg))) {
    pr_error("ioctl() failed. %s \n", strerror(errno));
  }
  return ret;
}