/*
 * PULP user-space runtime library
 *
 * Copyright 2018 ETH Zurich, University of Bologna
 *
 * Author: Pirmin Vogel <vogelpi@iis.ee.ethz.ch>
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
#include <stdio.h> // fclose(), fopen(), printf(), sprintf()
#include <stdlib.h> // free(), malloc()
#include <inttypes.h>
#include <sys/ioctl.h> // ioctl()
#include <time.h> // struct tm, localtime(), time(), time_t
#include <sys/stat.h> // fstat()
#include <errno.h>

#include "pulp.h"
#include "o1heap.h"

uint32_t pulp_read32(const uint32_t *base_addr, uint32_t off, char off_type)
{
  if (DEBUG_LEVEL > 4) {
    const uint32_t *addr;
    if (off_type == 'b')
      addr = base_addr + (off >> 2);
    else
      addr = base_addr + off;
    printf("Reading from %p\n", addr);
  }
  if (off_type == 'b')
    return *(base_addr + (off >> 2));
  else
    return *(base_addr + off);
}

void pulp_write32(uint32_t *base_addr, uint32_t off, char off_type, uint32_t value)
{
  if (DEBUG_LEVEL > 4) {
    uint32_t *addr;
    if (off_type == 'b')
      addr = base_addr + (off >> 2);
    else
      addr = base_addr + off;
    printf("Writing to %p\n", addr);
  }
  if (off_type == 'b')
    *(base_addr + (off >> 2)) = value;
  else
    *(base_addr + off) = value;
}

int pulp_mbox_read(const PulpDev *pulp, uint32_t *buffer, size_t n_words)
{
  int n_char, n_char_left, ret;
  ret = 1;
  n_char = 0;
  n_char_left = n_words * sizeof(buffer[0]);

  // read n_words words or until error
  while (n_char_left) {
    ret = read(pulp->fd, (char *)&buffer[n_char], n_char_left * sizeof(char));
    if (ret < 0) {
      printf("ERROR: Could not read mbox.\n");
      return ret;
    }
    n_char += ret;
    n_char_left -= ret;
  }

  return 0;
}

int pulp_mbox_write(PulpDev *pulp, uint32_t word)
{
  unsigned status = 1;
  unsigned us_delay = 100;

  // wait for not full
  while (status) {
    usleep(us_delay);
    status = pulp_read32(pulp->mbox.v_addr, MBOX_STATUS_OFFSET_B, 'b') & MBOX_STATUS_MASK_FULL;
  }

  // mbox is ready to receive
  pulp_write32(pulp->mbox.v_addr, MBOX_WRDATA_OFFSET_B, 'b', word);
  if (DEBUG_LEVEL > 3)
    printf("Wrote %#x to mbox.\n", word);

  return 0;
}

int pulp_reserve_v_addr(PulpDev *pulp)
{
  pulp->pulp_res_v_addr.size = PULP_SIZE_B;
  pulp->pulp_res_v_addr.v_addr = mmap((int *)ARCHI_CLUSTER_GLOBAL_ADDR(0), pulp->pulp_res_v_addr.size, PROT_NONE,
                                      MAP_PRIVATE | MAP_FIXED | MAP_ANONYMOUS, -1, 0);
  if (pulp->pulp_res_v_addr.v_addr == MAP_FAILED) {
    printf("MMAP failed to reserve virtual addresses overlapping with physical address map of PULP.\n");
    return -EIO;
  } else if (DEBUG_LEVEL > 0) {
    printf("Reserved virtual addresses starting at %p and overlapping with physical address map of PULP. \n",
           pulp->pulp_res_v_addr.v_addr);
  }

  pulp->l3_mem_res_v_addr.size = L3_MEM_SIZE_B;
  pulp->l3_mem_res_v_addr.v_addr =
    mmap((int *)L3_MEM_BASE_ADDR, pulp->l3_mem_res_v_addr.size, PROT_NONE, MAP_PRIVATE | MAP_FIXED | MAP_ANONYMOUS, -1, 0);
  if (pulp->l3_mem_res_v_addr.v_addr == MAP_FAILED) {
    printf("MMAP failed to reserve virtual addresses overlapping with physically contiguous L3 memory.\n");
    return -EIO;
  } else if (DEBUG_LEVEL > 0) {
    printf("Reserved virtual addresses starting at %p and overlapping with physically contiguous L3 memory.\n",
           pulp->l3_mem_res_v_addr.v_addr);
  }

  return 0;
}

int pulp_free_v_addr(const PulpDev *pulp)
{
  int status;

  if (DEBUG_LEVEL > 0)
    printf("Freeing reserved virtual addresses overlapping with physical address map of PULP.\n");
  status = munmap(pulp->pulp_res_v_addr.v_addr, pulp->pulp_res_v_addr.size);
  if (status) {
    printf("MUNMAP failed to free reserved virtual addresses overlapping with physical address map of PULP.\n");
    return -EINVAL;
  }

#if PLATFORM != JUNO
  if (DEBUG_LEVEL > 0)
    printf("Freeing reserved virtual addresses overlapping with with physically contiguous L3 memory.\n");
  status = munmap(pulp->l3_mem_res_v_addr.v_addr, pulp->l3_mem_res_v_addr.size);
  if (status) {
    printf("MUNMAP failed to free reserved virtual addresses overlapping with physically contiguous L3 memory.\n");
    return -EINVAL;
  }
#endif

  return 0;
}

void pulp_print_v_addr(PulpDev *pulp)
{
  // check the reservation
  printf("\nMemory map of the process:\n");
  printf("# cat /proc/getpid()/maps\n");

  char cmd[20];
  sprintf(cmd, "cat /proc/%i/maps", getpid());
  system(cmd);

  // check wether the reservation contributes to the kernels overcommit accounting -> Committed_AS
  printf("\nInformation about the system's memory:\n");
  printf("# cat /proc/meminfo\n");
  system("cat /proc/meminfo");

  return;
}

int pulp_mmap(PulpDev *pulp)
{
  int offset;

  /*
   *  open the device
   */
  pulp->fd = open("/dev/PULP", O_RDWR | O_SYNC);
  if (pulp->fd < 0) {
    printf("ERROR: Opening failed \n");
    return -ENOENT;
  }

  /*
   *  do the different remappings
   */
  // PULP internals
  // Clusters
  offset = 0; // start of clusters
  pulp->clusters.size = CLUSTERS_SIZE_B;

  pulp->clusters.v_addr = mmap(NULL, pulp->clusters.size, PROT_READ | PROT_WRITE, MAP_SHARED, pulp->fd, offset);
  if (pulp->clusters.v_addr == MAP_FAILED) {
    printf("MMAP failed for clusters.\n");
    return -EIO;
  } else if (DEBUG_LEVEL > 0) {
    printf("Clusters mapped to virtual user space at %p.\n", pulp->clusters.v_addr);
  }

  // SOC_PERIPHERALS
  offset = CLUSTERS_SIZE_B; // start of peripherals
  pulp->soc_periph.size = SOC_PERIPHERALS_SIZE_B;

  pulp->soc_periph.v_addr = mmap(NULL, pulp->soc_periph.size, PROT_READ | PROT_WRITE, MAP_SHARED, pulp->fd, offset);
  if (pulp->soc_periph.v_addr == MAP_FAILED) {
    printf("MMAP failed for SoC peripherals.\n");
    return -EIO;
  } else if (DEBUG_LEVEL > 0) {
    printf("SoC peripherals mapped to virtual user space at %p.\n", pulp->soc_periph.v_addr);
  }

  // Mailbox
  offset = CLUSTERS_SIZE_B + SOC_PERIPHERALS_SIZE_B; // start of mailbox
  pulp->mbox.size = MBOX_SIZE_B;

  pulp->mbox.v_addr = mmap(NULL, pulp->mbox.size, PROT_READ | PROT_WRITE, MAP_SHARED, pulp->fd, offset);
  if (pulp->mbox.v_addr == MAP_FAILED) {
    printf("MMAP failed for Mailbox.\n");
    return -EIO;
  } else if (DEBUG_LEVEL > 0) {
    printf("Mailbox mapped to virtual user space at %p.\n", pulp->mbox.v_addr);
  }

  // L2
  offset = CLUSTERS_SIZE_B + SOC_PERIPHERALS_SIZE_B + MBOX_SIZE_B; // start of L2
  pulp->l2_mem.size = L2_MEM_SIZE_B;

  pulp->l2_mem.v_addr = mmap(NULL, pulp->l2_mem.size, PROT_READ | PROT_WRITE, MAP_SHARED, pulp->fd, offset);

  if (pulp->l2_mem.v_addr == MAP_FAILED) {
    printf("MMAP failed for L2 memory.\n");
    return -EIO;
  } else if (DEBUG_LEVEL > 0) {
    printf("L2 memory mapped to virtual user space at %p.\n", pulp->l2_mem.v_addr);
  }

  // Platform
  // L3
  offset = CLUSTERS_SIZE_B + SOC_PERIPHERALS_SIZE_B + MBOX_SIZE_B + L2_MEM_SIZE_B; // start of L3
  pulp->l3_mem.size = L3_MEM_SIZE_B;

  pulp->l3_mem.v_addr = mmap(NULL, pulp->l3_mem.size, PROT_READ | PROT_WRITE, MAP_SHARED, pulp->fd, offset);
  if (pulp->l3_mem.v_addr == MAP_FAILED) {
    printf("MMAP failed for shared L3 memory.\n");
    return -EIO;
  } else if (DEBUG_LEVEL > 0) {
    printf("Shared L3 memory mapped to virtual user space at %p.\n", pulp->l3_mem.v_addr);
  }
  // FIXME: The size of the stdout buffer should be defined in the same place as for PULP.
  void* const l3_heap_base_v_addr = (void*)((uint8_t*)pulp->l3_mem.v_addr + 1024*1024);
  // Initialize L3 heap manager.
  pulp->l3_heap_mgr = o1heapInit(l3_heap_base_v_addr, L3_MEM_SIZE_B, NULL, NULL);
  if (pulp->l3_heap_mgr == NULL) {
    printf("Failed to initialize L3 heap manager.\n");
    return -ENOMEM;
  } else if (DEBUG_LEVEL > 0) {
    printf("Allocated L3 heap manager at %p.\n", pulp->l3_heap_mgr);
  }

  // PULP external
  // GPIO
  offset = CLUSTERS_SIZE_B + SOC_PERIPHERALS_SIZE_B + MBOX_SIZE_B + L2_MEM_SIZE_B + L3_MEM_SIZE_B; // start of GPIO
  pulp->gpio.size = H_GPIO_SIZE_B;

  pulp->gpio.v_addr = mmap(NULL, pulp->gpio.size, PROT_READ | PROT_WRITE, MAP_SHARED, pulp->fd, offset);
  if (pulp->gpio.v_addr == MAP_FAILED) {
    printf("MMAP failed for GPIO memory.\n");
    return -EIO;
  } else if (DEBUG_LEVEL > 0) {
    printf("GPIO memory mapped to virtual user space at %p.\n", pulp->gpio.v_addr);
  }

  // CLKING
  offset = CLUSTERS_SIZE_B + SOC_PERIPHERALS_SIZE_B + MBOX_SIZE_B + L2_MEM_SIZE_B + L3_MEM_SIZE_B +
           H_GPIO_SIZE_B; // start of Clking
  pulp->clking.size = CLKING_SIZE_B;

  pulp->clking.v_addr = mmap(NULL, pulp->clking.size, PROT_READ | PROT_WRITE, MAP_SHARED, pulp->fd, offset);
  if (pulp->clking.v_addr == MAP_FAILED) {
    if (errno == ENODEV) {
      if (DEBUG_LEVEL > 0) {
        printf("Device does not have a clock manager.\n");
      }
      pulp->clking.v_addr = NULL;
    } else {
      printf("MMAP failed for clock manager memory.\n");
      return -EIO;
    }
  } else if (DEBUG_LEVEL > 0) {
    printf("Clock Manager memory mapped to virtual user space at %p.\n", pulp->clking.v_addr);
  }

  // RAB config
  offset = CLUSTERS_SIZE_B + SOC_PERIPHERALS_SIZE_B + MBOX_SIZE_B + L2_MEM_SIZE_B + L3_MEM_SIZE_B + H_GPIO_SIZE_B +
           CLKING_SIZE_B; // start of RAB config
  pulp->rab_config.size = RAB_CONFIG_SIZE_B;

  pulp->rab_config.v_addr = mmap(NULL, pulp->rab_config.size, PROT_READ | PROT_WRITE, MAP_SHARED, pulp->fd, offset);
  if (pulp->rab_config.v_addr == MAP_FAILED) {
    printf("MMAP failed for shared L3 memory.\n");
    return -EIO;
  } else if (DEBUG_LEVEL > 0) {
    printf("RAB config memory mapped to virtual user space at %p.\n", pulp->rab_config.v_addr);
  }

#if PLATFORM == ZEDBOARD || PLATFORM == ZC706 || PLATFORM == MINI_ITX
  // SLCR
  offset = CLUSTERS_SIZE_B + SOC_PERIPHERALS_SIZE_B + MBOX_SIZE_B + L2_MEM_SIZE_B + L3_MEM_SIZE_B + H_GPIO_SIZE_B +
           CLKING_SIZE_B + RAB_CONFIG_SIZE_B; // start of SLCR
  pulp->slcr.size = SLCR_SIZE_B;

  pulp->slcr.v_addr = mmap(NULL, pulp->slcr.size, PROT_READ | PROT_WRITE, MAP_SHARED, pulp->fd, offset);
  if (pulp->slcr.v_addr == MAP_FAILED) {
    printf("MMAP failed for Zynq SLCR.\n");
    return -EIO;
  } else if (DEBUG_LEVEL > 0) {
    printf("Zynq SLCR memory mapped to virtual user space at %p.\n", pulp->slcr.v_addr);
  }
#endif

  return 0;
}

int pulp_munmap(PulpDev *pulp)
{
  unsigned status;

  // undo the memory mappings
  printf("Undo the memory mappings.\n");
#if PLATFORM == ZEDBOARD || PLATFORM == ZC706 || PLATFORM == MINI_ITX
  status = munmap(pulp->slcr.v_addr, pulp->slcr.size);
  if (status) {
    printf("MUNMAP failed for SLCR.\n");
    return -EINVAL;
  }
#endif
  status = munmap(pulp->gpio.v_addr, pulp->gpio.size);
  if (status) {
    printf("MUNMAP failed for GPIO.\n");
    return -EINVAL;
  }
  status = munmap(pulp->rab_config.v_addr, pulp->rab_config.size);
  if (status) {
    printf("MUNMAP failed for RAB config.\n");
    return -EINVAL;
  }
  status = munmap(pulp->l2_mem.v_addr, pulp->l2_mem.size);
  if (status) {
    printf("MUNMAP failed for L2 memory.\n");
    return -EINVAL;
  }
  status = munmap(pulp->soc_periph.v_addr, pulp->soc_periph.size);
  if (status) {
    printf("MUNMAP failed for SoC peripherals\n.");
    return -EINVAL;
  }
  status = munmap(pulp->clusters.v_addr, pulp->clusters.size);
  if (status) {
    printf("MUNMAP failed for clusters\n.");
    return -EINVAL;
  }
  status = munmap(pulp->l3_mem.v_addr, pulp->l3_mem.size);
  if (status) {
    printf("MUNMAP failed for shared L3 memory\n.");
    return -EINVAL;
  }

  // close the file descriptor
  printf("Close the file descriptor. \n");
  close(pulp->fd);
  pulp->fd = -1;

  return 0;
}

static int64_t read_int_from_file(const char *file)
{
  int64_t ret = 0;
  if (access(file, F_OK) == -1) {
    return -ENOENT;
  }
  FILE *fp;
  fp = fopen(file, "r");
  if (fp == NULL) {
    return -EPERM;
  }
  if (fscanf(fp, "%" PRId64, &ret) == 0) {
    fclose(fp);
    return -EIO;
  }
  fclose(fp);
  return ret;
}
static int write_int_to_file(const char *file, int64_t val)
{
  if (access(file, F_OK) == -1) {
    return -ENOENT;
  }
  FILE *fp;
  fp = fopen(file, "w");
  if (fp == NULL) {
    return -EPERM;
  }
  if (fprintf(fp, "%" PRId64, val) == 0) {
    fclose(fp);
    return -EIO;
  }
  fclose(fp);
  return 0;
}


int pulp_clking_set_freq(PulpDev *pulp, unsigned des_freq_mhz)
{
#if PLATFORM == ZYNQMP
  // FIXME: PULP clocking on ZynqMP is implemented in a separate driver
  int ret = write_int_to_file("/sys/class/fclkcfg/fclk0/rate", des_freq_mhz * 1000000ll);
  if(ret) {
    return ret;
  }
  ret = read_int_from_file("/sys/class/fclkcfg/fclk0/rate") / 1000000ll;
  pulp->pulp_clk_freq_mhz = ret;
  return ret;
#else
  int ret = ioctl(pulp->fd, PULP_IOCTL_CTRL_SET_FREQ, des_freq_mhz);
  pulp->pulp_clk_freq_mhz = ret;
  return ret;
#endif
}

int pulp_clking_measure_freq(PulpDev *pulp)
{
  // try to read host time info and clock counters
  int64_t host_time_diff = read_int_from_file("/sys/class/pmca/PULP/host_time_diff");
  int64_t pulp_clk_counter = read_int_from_file("/sys/class/pmca/PULP/accel_clk_diff");

  if (host_time_diff < 0 || pulp_clk_counter < 0) {
    return -EIO;
  }

  // save host frequency if available (FIXME: can be removed)
  int host_clk_freq_mhz = read_int_from_file("/sys/devices/system/cpu/cpufreq/policy0/cpuinfo_cur_freq");
  if (host_clk_freq_mhz > 0) {
    pulp->host_clk_freq_mhz = host_clk_freq_mhz;
  }

  // compute frequency
  return pulp_clk_counter / (host_time_diff / 1000);
}

int pulp_init(PulpDev *pulp)
{
  // set mbox mode to driver
  int err = ioctl(pulp->fd, PULP_IOCTL_MBOX_SET_MODE, MBOX_DRIVER);

  // check
  if (DEBUG_LEVEL > 1)
    printf("Mailbox interrupt enable register = %#x\n", pulp_read32(pulp->mbox.v_addr, MBOX_IE_OFFSET_B, 'b'));

  return err;
}

void pulp_reset(PulpDev *pulp, unsigned full)
{
  // Forward reset request to the driver
  ioctl(pulp->fd, PULP_IOCTL_CTRL_RESET, full);

  return;
}

int pulp_boot(PulpDev *pulp, const TaskDesc *task)
{
  int err;

  // load the binary
  err = pulp_load_bin(pulp, task->name);
  if (err) {
    printf("ERROR: Loading PULP binary failed.\n");
    return err;
  }

  // start execution
  pulp_exe_start(pulp);

  return 0;
}

int pulp_load_bin(PulpDev *pulp, const char *name)
{
  printf("Starting load...\n");

  int i;
  char *bin_name_tcdm;
  char *bin_name_l2;

#define MAX_PATH_LENGTH 32

  /*
   * prepare binary name
   */
  // remove anything after the first dot after last slash
  char *last_slash, *first_dot;
  last_slash = strrchr(name, '/');
  unsigned start, length;
  if (last_slash == NULL) {
    start = 0;
  } else {
    start = last_slash - name;
  }
  first_dot = strchr(name + start, '.');
  if (first_dot == NULL) {
    length = strlen(name);
  } else {
    length = first_dot - name;
  }

  // allocate memory for file names
  bin_name_tcdm = (char *)malloc((length + 1 + 9 + MAX_PATH_LENGTH) * sizeof(char));
  if (!bin_name_tcdm) {
    printf("ERROR: Malloc failed for bin_name_tcdm.\n");
    return -ENOMEM;
  }
  bin_name_l2 = (char *)malloc((length + 1 + 7 + MAX_PATH_LENGTH) * sizeof(char));
  if (!bin_name_l2) {
    printf("ERROR: Malloc failed for bin_name_l2.\n");
    return -ENOMEM;
  }

  // generate file names
  strncpy(bin_name_tcdm, name, length);
  bin_name_tcdm[length] = '\0';
  strcat(bin_name_tcdm, ".tcdm.bin");

  strncpy(bin_name_l2, name, length);
  bin_name_l2[length] = '\0';
  strcat(bin_name_l2, ".l2.bin");

  /*
   * load the binaries
   */
  int fd_tcdm, fd_l2;
  unsigned size_b_tcdm, size_b_l2;
  struct stat file_stats;
  unsigned *bin_tcdm, *bin_l2;
  unsigned status;
  unsigned has_tcdm_bin = 0;

  // TCDM
  // open TCDM bin file and get size if it exists
  if (access(bin_name_tcdm, F_OK) != -1) {
    has_tcdm_bin = 1;
    fd_tcdm = open(bin_name_tcdm, O_RDONLY);
    if (fd_tcdm < 0) {
      printf("ERROR: Could not open PULP binary %s.\n", bin_name_tcdm);
      return -ENOENT;
    }
    fstat(fd_tcdm, &file_stats);
    size_b_tcdm = file_stats.st_size;

    // memory map the binary, MAP_POPULATE makes sure there will be no page faults later on (DMA)
    bin_tcdm = (unsigned *)mmap(NULL, size_b_tcdm, PROT_READ, MAP_SHARED | MAP_POPULATE, fd_tcdm, 0);
    if (bin_tcdm == MAP_FAILED) {
      printf("MMAP failed for PULP binary %s.\n", bin_name_tcdm);
      return -EIO;
    }

    // write binary to TCDM
    if (DEBUG_LEVEL > 0)
      printf("Loading binary file: %s, size = %d B\n", bin_name_tcdm, size_b_tcdm);

    for (i = 0; i < size_b_tcdm / 4; i++)
      pulp->clusters.v_addr[i] = bin_tcdm[i];
  }

  // L2
  // open L2 bin file - alternatively, there is just one single binary .bin (legacy)
  if (access(bin_name_l2, F_OK) == -1) {
    bin_name_l2[0] = '\0';
    strncpy(bin_name_l2, name, length);
    bin_name_l2[length] = '\0';
    strcat(bin_name_l2, ".bin");
  }

  // open TCDM bin file and get size
  fd_l2 = open(bin_name_l2, O_RDONLY);
  if (fd_l2 < 0) {
    printf("ERROR: Could not open PULP binary %s.\n", bin_name_l2);
    return -ENOENT;
  }
  fstat(fd_l2, &file_stats);
  size_b_l2 = file_stats.st_size;

  // memory map the binary, MAP_POPULATE makes sure there will be no page faults later on (DMA)
  bin_l2 = (unsigned *)mmap(NULL, size_b_l2, PROT_READ, MAP_SHARED | MAP_POPULATE, fd_l2, 0);
  if (bin_l2 == MAP_FAILED) {
    printf("MMAP failed for PULP binary %s.\n", bin_name_l2);
    return -EIO;
  }

  // write binary to L2
  if (DEBUG_LEVEL > 0)
    printf("Loading binary file: %s, size = %d B\n", bin_name_l2, size_b_l2);

  for (i = 0; i < size_b_l2 / 4; i++)
    pulp->l2_mem.v_addr[i] = bin_l2[i];

  /*
   * check the binaries
   */
  if (DEBUG_LEVEL > 0) {
    int j;
    int n_failed;

    // TCDM
    if (has_tcdm_bin) {
      n_failed = 0;

      for (j = 0; j < size_b_tcdm / 4; j++) {
        if (pulp->clusters.v_addr[j] != bin_tcdm[j]) {
          n_failed++;
        }
      }
      if (n_failed)
        printf("WARNING: PULP binary %s not successfully copied to TCDM. Failed for %i/%i words.\n", bin_name_tcdm, n_failed,
               size_b_tcdm / 4);
      else
        printf("PULP binary %s successfully copied to TCDM.\n", bin_name_tcdm);
    }

    // L2
    n_failed = 0;
    for (j = 0; j < size_b_l2 / 4; j++) {
      if (pulp->l2_mem.v_addr[j] != bin_l2[j]) {
        n_failed++;
      }
    }
    if (n_failed)
      printf("WARNING: PULP binary %s not successfully copied to L2. Failed for %i/%i words.\n", bin_name_l2, n_failed,
             size_b_l2 / 4);
    else
      printf("PULP binary %s successfully copied to L2.\n", bin_name_l2);
  }

  /*
   * cleanup
   */
  if (has_tcdm_bin) {
    status = munmap(bin_tcdm, size_b_tcdm);
    if (status) {
      printf("MUNMAP failed for PULP binary.\n");
    }
    close(fd_tcdm);
  }

  status = munmap(bin_l2, size_b_l2);
  if (status) {
    printf("MUNMAP failed for PULP binary.\n");
  }
  close(fd_l2);

  free(bin_name_tcdm);
  free(bin_name_l2);

  return 0;
}

int pulp_load_bin_from_mem(PulpDev *pulp, void *ptr, unsigned size)
{
  unsigned int *intptr = (unsigned int *)ptr;
  unsigned i;

  // write binary to L2
  for (i = 0; i < size / 0x4U; i++)
    pulp->l2_mem.v_addr[i] = intptr[i];

  return 0;
}

void pulp_exe_start(PulpDev *pulp)
{
  printf("Starting program execution.\n");

  // Forward activation of all clusters to the driver
  pulp->cluster_sel = CLUSTER_MASK;
  ioctl(pulp->fd, PULP_IOCTL_CTRL_START, pulp->cluster_sel);
}

void pulp_exe_stop(PulpDev *pulp)
{
  printf("Stopping program execution.\n");

  // Forward deactivation of all running cluster to the driver
  ioctl(pulp->fd, PULP_IOCTL_CTRL_STOP, pulp->cluster_sel);
  pulp->cluster_sel = 0;
}

int pulp_exe_wait(const PulpDev *pulp, int timeout_s)
{
  int timeout = timeout_s * 1000;

  return ioctl(pulp->fd, PULP_IOCTL_CTRL_WAIT, timeout);
}

int pulp_rab_req(const PulpDev *pulp, unsigned addr_start, unsigned size_b, unsigned char prot, unsigned char port,
                 unsigned char date_exp, unsigned char date_cur, unsigned char use_acp, unsigned char rab_lvl)
{
  int err;
  unsigned request[3];

  // setup the request
  request[0] = 0;
  RAB_SET_PROT(request[0], prot);
  RAB_SET_ACP(request[0], use_acp);
  RAB_SET_PORT(request[0], port);
  RAB_SET_LVL(request[0], rab_lvl);
  RAB_SET_DATE_EXP(request[0], date_exp);
  RAB_SET_DATE_CUR(request[0], date_cur);
  request[1] = addr_start;
  request[2] = size_b;

  // make the request
  err = ioctl(pulp->fd, PULP_IOCTL_RAB_REQ, request);
  if (err) {
    printf("ERROR: ioctl for RAB request failed. err = %d, errno = %d\n", err, errno);
  }

  return err;
}

void pulp_rab_free(const PulpDev *pulp, unsigned char date_cur)
{
  // make the request
  ioctl(pulp->fd, PULP_IOCTL_RAB_FREE, (unsigned)date_cur);
}

int pulp_rab_req_striped(const PulpDev *pulp, const TaskDesc *task, ElemPassType **pass_type, int n_elements)
{
  int i, j, k, err;
  unsigned n_data;

  n_data = task->n_data;

  RabStripeReqUser stripe_request;

  stripe_request.id = 0;
  stripe_request.n_elements = (short)n_elements;

  RabStripeElemUser *elements =
    (RabStripeElemUser *)malloc((unsigned)(stripe_request.n_elements * sizeof(RabStripeElemUser)));
  if (elements == NULL) {
    printf("ERROR: Malloc failed for RabStripeElemUser structs.\n");
    return -ENOMEM;
  }

  stripe_request.rab_stripe_elem_user_addr = (unsigned long)&elements[0];

  unsigned *addr_start;
  unsigned *addr_end;

  unsigned flags, prot;
  unsigned offset_start, size_b;
  unsigned max_stripe_size_b, overlap;

  offset_start = 0;
  size_b = 0;

  /*
   * fill stripe elements - except actual addresses - these are filled later
   */
  j = 0;
  for (i = 0; i < n_data; i++) {
    if ((task->data_desc[i].sh_mem_ctrl) == 2) {
      // determine max_stripe_size_b
      max_stripe_size_b = task->data_desc[i].stripe_desc->first_stripe_size_b;
      if (task->data_desc[i].stripe_desc->last_stripe_size_b > max_stripe_size_b)
        max_stripe_size_b = task->data_desc[i].stripe_desc->last_stripe_size_b;
      if (task->data_desc[i].stripe_desc->stripe_size_b > max_stripe_size_b)
        max_stripe_size_b = task->data_desc[i].stripe_desc->stripe_size_b;

      // fill stripe elements
      elements[j].max_stripe_size_b = max_stripe_size_b;
      elements[j].n_stripes = task->data_desc[i].stripe_desc->n_stripes;

      if (DEBUG_LEVEL > 2) {
        printf("size of striped element %d     = %#x\n", j, task->data_desc[i].size);
        printf("elements[%d].n_stripes         = %d\n", j, elements[j].n_stripes);
        printf("elements[%d].max_stripe_size_b = %#x\n", j, elements[j].max_stripe_size_b);
      }

      j++;
    } // if
  } // for

  /*
   * generate address tables
   */
  i = -1;
  for (k = 0; k < n_data; k++) {
    if ((task->data_desc[k].sh_mem_ctrl) == 2) {
      i++;

      // set protection and cache ctrl flags
      flags = 0;
      if (task->data_desc[k].type == in) // in = read
        prot = 0x2 | 0x1;
      else if (task->data_desc[k].type == out) // out = write
        prot = 0x4 | 0x1;
      else // 0: inout = read & write
        prot = 0x4 | 0x2 | 0x1;
      RAB_SET_PROT(flags, prot);
      RAB_SET_ACP(flags, task->data_desc[k].cache_ctrl);

      elements[i].id = (unsigned char)i; // not used right now
      elements[i].type = (unsigned char)(task->data_desc[k].type);
      elements[i].flags = (unsigned char)flags;

      // allocate memory to hold striping information
      addr_start = (unsigned *)malloc((unsigned)elements[i].n_stripes * sizeof(unsigned));
      addr_end = (unsigned *)malloc((unsigned)elements[i].n_stripes * sizeof(unsigned));
      if ((addr_start == NULL) || (addr_end == NULL)) {
        printf("ERROR: Malloc failed for addr_start/addr_end.\n");
        return -ENOMEM;
      }

      // fill pointer values
      elements[i].stripe_addr_start = (unsigned long)&addr_start[0];
      elements[i].stripe_addr_end = (unsigned long)&addr_end[0];

      // some apps need an overlap in some elements
      overlap = 0;
      if (!strcmp(task->name, "rod")) {
        if (task->data_desc[k].type == in) // input elements are overlapped only

          overlap = 2 * sizeof(unsigned char) * (3 * (*(unsigned *)(task->data_desc[3].ptr))); // (R * w);
      } // if

      // fill in stripe data
      for (j = 0; j < elements[i].n_stripes; j++) {
        if (j == 0) {
          // first stripe
          offset_start = 0;
          size_b = task->data_desc[i].stripe_desc->first_stripe_size_b;
        } else if (j == (elements[i].n_stripes - 1)) {
          // last stripe
          offset_start += (size_b - overlap);
          size_b = task->data_desc[i].stripe_desc->last_stripe_size_b;
        } else {
          // intermediate stripes
          offset_start += (size_b - overlap);
          size_b = task->data_desc[i].stripe_desc->stripe_size_b;
        }

        // write the address arrays
        addr_start[j] = (unsigned long)(task->data_desc[k].ptr) + offset_start;
        addr_end[j] = addr_start[j] + size_b;
      } // for n_stripes

      if (DEBUG_LEVEL > 2) {
        printf("Shared Element %d: \n", k);
        printf("stripe_addr_start @ %#lx\n", elements[i].stripe_addr_start);
        printf("stripe_addr_end   @ %#lx\n", elements[i].stripe_addr_end);
        for (j = 0; j < elements[i].n_stripes; j++) {
          if (j > 2 && j < (elements[i].n_stripes - 3))
            continue;
          printf("%d\t", j);
          printf("%#x - ", ((unsigned *)(elements[i].stripe_addr_start))[j]);
          printf("%#x\n", ((unsigned *)(elements[i].stripe_addr_end))[j]);
        }
        printf("\n");
      } // DEBUG_LEVEL > 2
    } // sh_mem_ctrl == 2
  } // for n_data

  // make the request
  err = ioctl(pulp->fd, PULP_IOCTL_RAB_REQ_STRIPED, (unsigned *)&stripe_request);
  if (err) {
    printf("ERROR: ioctl() for stripe request failed. err = %d, errno = %d\n", err, errno);
  }

  // free memory
  for (i = 0; i < stripe_request.n_elements; i++) {
    free((unsigned *)elements[i].stripe_addr_start);
    free((unsigned *)elements[i].stripe_addr_end);
  }
  free(elements);

  return err;
}

void pulp_rab_free_striped(const PulpDev *pulp)
{
  unsigned offload_id = 0;

  // make the request
  ioctl(pulp->fd, PULP_IOCTL_RAB_FREE_STRIPED, offload_id);
}

int pulp_rab_soc_mh_enable(const PulpDev *pulp, const unsigned static_2nd_lvl_slices)
{
  unsigned request[2];
  request[0] = MH_ACCEL;
  request[1] = static_2nd_lvl_slices & 1;
  return ioctl(pulp->fd, PULP_IOCTL_VM_SET_MH_MODE, request);
}

// FIXME: remove function and return to MH_NONE mode
int pulp_rab_soc_mh_disable(const PulpDev *const pulp)
{
  unsigned request[1];
  request[0] = MH_NONE;
  return ioctl(pulp->fd, PULP_IOCTL_VM_SET_MH_MODE, request);
}

int pulp_rab_mh_enable(const PulpDev *pulp, unsigned char use_acp, unsigned char rab_mh_lvl)
{
  unsigned request[3];
  request[0] = MH_HOST_RAB;
  request[1] = (unsigned)use_acp;
  request[2] = (unsigned)rab_mh_lvl;
  return ioctl(pulp->fd, PULP_IOCTL_VM_SET_MH_MODE, request);
}

// FIXME: remove function and return to MH_NONE mode
int pulp_rab_mh_disable(const PulpDev *pulp)
{
  unsigned request[1];
  request[0] = MH_NONE;
  return ioctl(pulp->fd, PULP_IOCTL_VM_SET_MH_MODE, request);
}

int pulp_smmu_enable(const PulpDev *pulp, const unsigned char flags)
{
  unsigned request[2];
  request[0] = MH_HOST_SMMU;
  request[1] = flags;
  return ioctl(pulp->fd, PULP_IOCTL_VM_SET_MH_MODE, request);
}

// FIXME: remove function and return to MH_NONE mode
int pulp_smmu_disable(const PulpDev *pulp)
{
  unsigned request[1];
  request[0] = MH_NONE;
  return ioctl(pulp->fd, PULP_IOCTL_VM_SET_MH_MODE, request);
}

int pulp_rab_ax_log_read(const PulpDev *const pulp)
{
  int err = 0;

#if RAB_AX_LOG_EN == 1
  // allocate memory for ptrs
  unsigned **ptrs = (unsigned **)malloc(4 * sizeof(unsigned *));
  if (!ptrs) {
    printf("ERROR: Malloc failed for ptrs.\n");
    return -ENOMEM;
  }

  // allocate memory for status
  unsigned *status = (unsigned *)malloc(3 * sizeof(unsigned));
  if (!status) {
    printf("ERROR: Malloc failed for status.\n");
    return -ENOMEM;
  }

  // allocate the buffers in user space
  unsigned *rab_ar_log_buf = (unsigned *)malloc(RAB_AX_LOG_BUF_SIZE_B);
  unsigned *rab_aw_log_buf = (unsigned *)malloc(RAB_AX_LOG_BUF_SIZE_B);
  unsigned *rab_cfg_log_buf = (unsigned *)malloc(RAB_AX_LOG_BUF_SIZE_B);
  if ((rab_ar_log_buf == NULL) || (rab_aw_log_buf == NULL) || (rab_cfg_log_buf == NULL)) {
    printf("ERROR: Malloc failed for rab_ar_log_buf/rab_aw_log_buf/rab_cfg_log_buf.\n");
    return -ENOMEM;
  }
  memset((void *)rab_ar_log_buf, 0, (unsigned)RAB_AX_LOG_BUF_SIZE_B);
  memset((void *)rab_aw_log_buf, 0, (unsigned)RAB_AX_LOG_BUF_SIZE_B);
  memset((void *)rab_cfg_log_buf, 0, (unsigned)RAB_AX_LOG_BUF_SIZE_B);

  ptrs[0] = &status[0];
  ptrs[1] = &rab_ar_log_buf[0];
  ptrs[2] = &rab_aw_log_buf[0];
  ptrs[3] = &rab_cfg_log_buf[0];

  // get the data from kernel space
  err = ioctl(pulp->fd, PULP_IOCTL_RAB_AX_LOG_READ, &ptrs[0]);
  if (err) {
    printf("ERROR: ioctl for RAB AX log read failed. err = %d, errno = %d\n", err, errno);
  }

  // Obtain the current date and time for the file name.
  const time_t t = time(NULL);
  if (t < 0) {
    printf("ERROR: Could not get time!\n");
    return -ENODATA;
  }
  const struct tm *const lt = localtime(&t);
  if (lt == NULL) {
    printf("ERROR: Could not convert time to local time!\n");
    return -ENODATA;
  }
  char lt_str[20];
  sprintf(lt_str, "%04d-%02d-%02d_%02d-%02d-%02d", lt->tm_year + 1900, lt->tm_mon + 1, lt->tm_mday, lt->tm_hour, lt->tm_min,
          lt->tm_sec);
  char filename[64];
  sprintf(filename, "rab_ax_log_%s.txt", lt_str);

  // write the data to a file
  FILE *fp;
  if ((fp = fopen(filename, "w")) == NULL) {
    printf("ERROR: Could not open RAB AX log file.\n");
    return -ENOENT;
  }

  unsigned ar_idx = 0;
  unsigned aw_idx = 0;
  unsigned cfg_idx = 0;
  unsigned ar_idx_max = status[0];
  unsigned aw_idx_max = status[1];
  unsigned cfg_idx_max = status[2];

  unsigned ts, meta, addr, len, id, type;
  unsigned ar_ts = 0, ar_meta = 0, ar_addr = 0;
  unsigned aw_ts = 0, aw_meta = 0, aw_addr = 0;

  type = 0;

  // TODO: sorting of cfg
  // (really necessary? what if we also want to add the read/write response buffers?)
  while ((ar_idx + aw_idx) < (ar_idx_max + aw_idx_max)) {
    // read next entry from buffers
    if (ar_idx < ar_idx_max) {
      ar_ts = rab_ar_log_buf[ar_idx + 0];
      ar_meta = rab_ar_log_buf[ar_idx + 1];
      ar_addr = rab_ar_log_buf[ar_idx + 2];
    }
    if (aw_idx < aw_idx_max) {
      aw_ts = rab_aw_log_buf[aw_idx + 0];
      aw_meta = rab_aw_log_buf[aw_idx + 1];
      aw_addr = rab_aw_log_buf[aw_idx + 2];
    }

    // determine which entry to write to log file
    if ((ar_idx < ar_idx_max) && (aw_idx < aw_idx_max)) { // both buffers have valid entries
      if (ar_ts < aw_ts) {
        ts = ar_ts;
        meta = ar_meta;
        addr = ar_addr;
        ar_idx += 3;
        type = 0;
      } else {
        ts = aw_ts;
        meta = aw_meta;
        addr = aw_addr;
        aw_idx += 3;
        type = 1;
      }
    } else {
      if (ar_idx < ar_idx_max) {
        ts = ar_ts;
        meta = ar_meta;
        addr = ar_addr;
        ar_idx += 3;
        type = 0;
      } else { // aw_idx < aw_idx_max
        ts = aw_ts;
        meta = aw_meta;
        addr = aw_addr;
        aw_idx += 3;
        type = 1;
      }
    }

    // write the entry into the log file
    len = BF_GET(meta, 0, 8);
    id = BF_GET(meta, 8, 10);
  #if RAB_AX_LOG_PRINT_FORMAT == 0 // DEBUG
    fprintf(fp, "%10u 0x%08x %3u 0x%03x %u\n", ts, addr, len, id, type);
  #else // 1 = MATLAB
    fprintf(fp, "%u %u %u %u %u\n", ts, addr, len, id, type);
  #endif
  }

  for (cfg_idx = 0; cfg_idx < cfg_idx_max; cfg_idx += 3) {
    type = 2;
    ts = rab_cfg_log_buf[cfg_idx + 0];
    meta = rab_cfg_log_buf[cfg_idx + 1];
    addr = rab_cfg_log_buf[cfg_idx + 2];
    len = BF_GET(meta, 0, 8);
    id = BF_GET(meta, 8, 10);
  #if RAB_AX_LOG_PRINT_FORMAT == 0 // DEBUG
    fprintf(fp, "%10u 0x%08x %3u 0x%03x %u\n", ts, addr, len, id, type);
  #else // 1 = MATLAB
    fprintf(fp, "%u %u %u %u %u\n", ts, addr, len, id, type);
  #endif
  }

  fclose(fp);

  // free the buffers
  free(rab_aw_log_buf);
  free(rab_ar_log_buf);
  free(rab_cfg_log_buf);
  free(status);
  free(ptrs);

#endif

  return err;
}

int pulp_profile_info(const PulpDev *pulp, ProfileInfo *profile_info)
{
  return ioctl(pulp->fd, PULP_IOCTL_INFO_PROFILE, profile_info);
}

int pulp_offload_out(PulpDev *pulp, TaskDesc *task)
{
  int n_ref, err;
  ElemPassType *pass_type;

  pass_type = (ElemPassType *)malloc(task->n_data * sizeof(ElemPassType));
  if (pass_type == NULL) {
    printf("ERROR: Malloc failed for pass_type.\n");
    return -ENOMEM;
  }

  // only remap addresses belonging to data elements larger than 32 bit
  n_ref = pulp_offload_get_pass_type(task, &pass_type);

  // RAB setup
  err = pulp_offload_rab_setup(pulp, task, &pass_type, n_ref);
  if (err) {
    printf("ERROR: pulp_offload_rab_setup failed.\n");
    return err;
  }

  // copy raw data out to contiguous L3 - pointers inside the data are not modified
  err = pulp_offload_l3_copy_raw_out(pulp, task, (const ElemPassType **)&pass_type);
  if (err) {
    printf("ERROR: pulp_offload_l3_copy_raw_out failed.\n");
    return err;
  }

  // pass data descriptor to PULP
  err = pulp_offload_pass_desc(pulp, task, (const ElemPassType **)&pass_type);
  if (err) {
    printf("ERROR: pulp_offload_pass_desc failed.\n");
    return err;
  }

  // free memory
  free(pass_type);

  return 0;
}

int pulp_offload_in(PulpDev *pulp, TaskDesc *task)
{
  int n_ref, err;
  ElemPassType *pass_type;

  pass_type = (ElemPassType *)malloc(task->n_data * sizeof(ElemPassType));
  if (pass_type == NULL) {
    printf("ERROR: Malloc failed for pass_type.\n");
    return -ENOMEM;
  }

  // read back data elements with sizes up to 32 bit from mbox
  n_ref = pulp_offload_get_pass_type(task, &pass_type);

  // RAB free
  err = pulp_offload_rab_free(pulp, task, (const ElemPassType **)&pass_type, n_ref);
  if (err) {
    printf("ERROR: pulp_offload_rab_free failed.\n");
    return err;
  }

  // copy raw data in from contiguous L3 - pointers inside the data are not modified
  err = pulp_offload_l3_copy_raw_in(pulp, task, (const ElemPassType **)&pass_type);
  if (err) {
    printf("ERROR: pulp_offload_l3_copy_raw_in failed.\n");
    return err;
  }

  // fetch values of data elements passed by value
  err = pulp_offload_get_desc(pulp, task, (const ElemPassType **)&pass_type);
  if (err) {
    printf("ERROR: pulp_offload_get_desc failed.\n");
    return err;
  }

  // free memory
  free(pass_type);

  return 0;
}

int pulp_offload_get_pass_type(const TaskDesc *task, ElemPassType **pass_type)
{
  int i, n_data, n_ref, size_b;

  n_data = task->n_data;
  n_ref = 0;
  size_b = sizeof(unsigned);

  for (i = 0; i < n_data; i++) {
    if (task->data_desc[i].size > size_b) {
      switch (task->data_desc[i].sh_mem_ctrl) {
      case copy:
        (*pass_type)[i] = ref_copy;
        break;

      case svm_static:
        (*pass_type)[i] = ref_svm_static;
        break;

      case svm_stripe:
        (*pass_type)[i] = ref_svm_stripe;
        break;

      case svm_mh:
        (*pass_type)[i] = ref_svm_mh;
        break;

      case copy_tryx:
        (*pass_type)[i] = ref_copy; // the runtime maps ref_copy_tryx to ref_copy
        break;

      case svm_smmu:
        (*pass_type)[i] = ref_svm_mh; // the miss handling is performed by the SMMU
        break;

      case svm_smmu_shpt:
        (*pass_type)[i] = ref_copy; // the runtime maps ref_svm_smmu_shpt to ref_copy
        break;

      case custom:
        (*pass_type)[i] = ref_custom;
        break;

      default:
        break;

        n_ref++;
      }
    } else
      (*pass_type)[i] = val;
  }

  return n_ref;
}

int pulp_offload_rab_setup(const PulpDev *pulp, const TaskDesc *task, ElemPassType **pass_type, int n_ref)
{
  int i, j, err;
  unsigned n_ref_svm_static, n_ref_svm_stripe;
  unsigned n_data, n_data_int, gap_size, temp;
  unsigned char prot, port, date_cur, date_exp;

  unsigned *v_addr_int;
  unsigned *size_int;
  unsigned *order;
  unsigned char *cache_ctrl_int;
  unsigned char *rab_lvl_int;
  unsigned char *prot_int;

  n_data = task->n_data;

  date_cur = (unsigned char)(task->task_id + 1);
  date_exp = (unsigned char)(task->task_id + 30);

  n_ref_svm_static = 0;
  n_ref_svm_stripe = 0;

  // determine number of elements to pass in which form
  for (i = 0; i < n_data; i++) {
    if ((*pass_type)[i] == ref_svm_static)
      n_ref_svm_static++;
    else if ((*pass_type)[i] == ref_svm_stripe)
      n_ref_svm_stripe++;
  }

  if (DEBUG_LEVEL > 1) {
    printf("n_ref_svm_static = %d, n_ref_svm_stripe = %d\n", n_ref_svm_static, n_ref_svm_stripe);
  }

  /*
   *  set up regular RAB slices
   */
  if (n_ref_svm_static) {
    port = 1;
    n_data_int = 1;

    // memory allocation for intervals
    v_addr_int = (unsigned *)malloc((unsigned)n_ref_svm_static * sizeof(unsigned));
    size_int = (unsigned *)malloc((unsigned)n_ref_svm_static * sizeof(unsigned));
    order = (unsigned *)malloc((unsigned)n_ref_svm_static * sizeof(unsigned));
    cache_ctrl_int = (unsigned char *)malloc((unsigned)n_ref_svm_static * sizeof(unsigned char));
    rab_lvl_int = (unsigned char *)malloc((unsigned)n_ref_svm_static * sizeof(unsigned char));
    prot_int = (unsigned char *)malloc((unsigned)n_ref_svm_static * sizeof(unsigned char));
    if (!v_addr_int | !size_int | !order | !cache_ctrl_int | !rab_lvl_int) {
      printf("Malloc failed for RAB setup.\n");
      return -ENOMEM;
    }

    // select the elements to order
    j = 0;
    for (i = 0; i < n_data; i++) {
      if ((*pass_type)[i] == ref_svm_static) {
        order[j] = i;
        j++;
      }
    }

    // order the elements - bubble sort
    for (i = n_ref_svm_static; i > 1; i--) {
      for (j = 0; j < i - 1; j++) {
        if (task->data_desc[j].ptr > task->data_desc[j + 1].ptr) {
          temp = order[j];
          order[j] = order[j + 1];
          order[j + 1] = temp;
        }
      }
    }
    if (DEBUG_LEVEL > 2) {
      printf("Reordered %d data elements: \n", n_ref_svm_static);
      for (i = 0; i < n_ref_svm_static; i++) {
        printf("%d \t %p \t %#x \n", order[i], task->data_desc[order[i]].ptr, task->data_desc[order[i]].size);
      }
    }

    // determine the number of remappings/intervals to request
    v_addr_int[0] = (unsigned long)task->data_desc[order[0]].ptr;
    size_int[0] = (unsigned long)task->data_desc[order[0]].size;
    cache_ctrl_int[0] = task->data_desc[order[0]].cache_ctrl;
    rab_lvl_int[0] = task->data_desc[order[0]].rab_lvl;
    if (task->data_desc[order[0]].type == inout) // input & output
      prot_int[0] = 0x7; // read & write
    else if (task->data_desc[order[0]].type == in) // input only
      prot_int[0] = 0x3; // read only
    else
      prot_int[0] = 0x5; // write only

    for (i = 1; i < n_ref_svm_static; i++) {
      j = order[i];
      gap_size = (unsigned long)task->data_desc[j].ptr - (v_addr_int[n_data_int - 1] + size_int[n_data_int - 1]);

      if (task->data_desc[j].type == inout) // input & output
        prot = 0x7; // read & write
      else if (task->data_desc[j].type == in) // input only
        prot = 0x3; // read only
      else
        prot = 0x5; // write only

      if (gap_size > RAB_CONFIG_MAX_GAP_SIZE_B || prot != prot_int[n_data_int - 1] ||
          task->data_desc[j].cache_ctrl != cache_ctrl_int[n_data_int - 1] ||
          task->data_desc[j].rab_lvl != rab_lvl_int[n_data_int - 1]) {
        // gap too large, different prot, different cache ctrl setting, different RAB level
        // -> create a new interval/mapping
        n_data_int++;
        v_addr_int[n_data_int - 1] = (unsigned long)task->data_desc[j].ptr;
        size_int[n_data_int - 1] = (unsigned long)task->data_desc[j].size;
        cache_ctrl_int[n_data_int - 1] = task->data_desc[j].cache_ctrl;
        rab_lvl_int[n_data_int - 1] = task->data_desc[j].rab_lvl;
        prot_int[n_data_int - 1] = prot;
      } else {
        // extend the previous mapping
        size_int[n_data_int - 1] += (gap_size + task->data_desc[j].size);
      }
    }

    // set up the RAB
    if (DEBUG_LEVEL > 2) {
      printf("Requesting %d remapping(s):\n", n_data_int);
    }
    for (i = 0; i < n_data_int; i++) {
      if (DEBUG_LEVEL > 2) {
        printf("%d \t %#x \t %#x \n", i, v_addr_int[i], size_int[i]);
        usleep(1000000);
      }
      pulp_rab_req(pulp, v_addr_int[i], size_int[i], prot_int[i], port, date_exp, date_cur, cache_ctrl_int[i],
                   rab_lvl_int[i]);
    }

    // free memory
    free(v_addr_int);
    free(size_int);
    free(cache_ctrl_int);
    free(rab_lvl_int);
    free(prot_int);
    free(order);
  }

  /*
   * set up striped RAB slices
   */
  if (n_ref_svm_stripe) {
    err = pulp_rab_req_striped(pulp, task, pass_type, n_ref_svm_stripe);
    if (err) {
      printf("Requesting striped RAB mappings failed: %d\n", err);
      return err;
    }
  }

  return 0;
}

int pulp_offload_rab_free(const PulpDev *pulp, const TaskDesc *task, const ElemPassType **pass_type, int n_ref)
{
  int i;
  unsigned n_ref_svm_static, n_ref_svm_stripe;
  unsigned n_data;
  unsigned char date_cur;

  n_data = task->n_data;

  date_cur = (unsigned char)(task->task_id + 41);

  n_ref_svm_static = 0;
  n_ref_svm_stripe = 0;

  // determine number of elements to passed in which form
  for (i = 0; i < n_data; i++) {
    if ((*pass_type)[i] == ref_svm_static)
      n_ref_svm_static++;
    else if ((*pass_type)[i] == ref_svm_stripe)
      n_ref_svm_stripe++;
  }

  // free regular RAB slices
  if (n_ref_svm_static) {
    pulp_rab_free(pulp, date_cur);
  }

  // free striped RAB slices
  if (n_ref_svm_stripe) {
    pulp_rab_free_striped(pulp);
  }

  return 0;
}

int pulp_offload_pass_desc(PulpDev *pulp, const TaskDesc *task, const ElemPassType **pass_type)
{
  int i;
  unsigned n_data;
  uintptr_t addr;

  n_data = task->n_data;

  if (DEBUG_LEVEL > 2) {
    printf("Mailbox status = %#x.\n", pulp_read32(pulp->mbox.v_addr, MBOX_STATUS_OFFSET_B, 'b'));
  }

  for (i = 0; i < n_data; i++) {
    if ((*pass_type)[i]) {
      // pass data element by reference
      if (((*pass_type)[i] == ref_copy) || ((*pass_type)[i] == ref_custom))
        addr = (uintptr_t)(task->data_desc[i].ptr_l3_p); // pass phys addr in contiguous L3
      else
        addr = (uintptr_t)(task->data_desc[i].ptr); // pass virt addr

      pulp_mbox_write(pulp, addr);
      if (DEBUG_LEVEL > 2)
        printf("Element %d: wrote addr %#lx to mbox.\n", i, addr);
    } else {
      // pass data element by value and of type input/output or input
      if ((task->data_desc[i].type == inout) || (task->data_desc[i].type == in)) {
        pulp_mbox_write(pulp, *(unsigned *)(task->data_desc[i].ptr));
        if (DEBUG_LEVEL > 2)
          printf("Element %d: wrote val  %#x to mbox.\n", i, *(unsigned *)(task->data_desc[i].ptr));
      } else { // pass by value, but type is output only
        if (DEBUG_LEVEL > 2)
          printf("Element %d: not passed to mbox.\n", i);
      }
    }
  }

  return 0;
}

int pulp_offload_get_desc(const PulpDev *pulp, TaskDesc *task, const ElemPassType **pass_type)
{
  int i, j, n_data, n_values, ret;
  unsigned *buffer;

  j = 0;
  n_data = task->n_data;
  n_values = 0;
  ret = 0;

  for (i = 0; i < n_data; i++) {
    // check if argument has been passed by value and is of type output or input and output
    if (((*pass_type)[i] == val) && ((task->data_desc[i].type == inout) || (task->data_desc[i].type == out))) {
      n_values++;
    }
  }

  buffer = (unsigned *)malloc(n_values * sizeof(unsigned));
  if (buffer == NULL) {
    printf("ERROR: Malloc failed for buffer.\n");
    return -ENOMEM;
  }

  // read from mbox
  pulp_mbox_read(pulp, &buffer[0], n_values);

  for (i = 0; i < n_data; i++) {
    // check if argument has been passed by value and is of type input/output or output
    if (((*pass_type)[i] == val) && ((task->data_desc[i].type == inout) || (task->data_desc[i].type == out))) {
      // read from buffer
      *(unsigned *)(task->data_desc[i].ptr) = buffer[j];
      j++;
    }
  }

  if (j != n_values) {
    printf("ERROR: Got back only %d of %d data elements from PULP.\n", j, n_values);
    ret = -EIO;
  }

  //#ifndef JPEG // generates error
  free(buffer);
  //#endif

  return ret;
}

int pulp_offload_l3_copy_raw_out(PulpDev *pulp, TaskDesc *task, const ElemPassType **pass_type)
{
  int i;
  unsigned n_ref_copy;
  int n_data;
  ElemType type;
  unsigned size;

  n_data = task->n_data;

  n_ref_copy = 0;

  // determine number of elements to pass in which form
  for (i = 0; i < n_data; i++) {
    if ((*pass_type)[i] == ref_copy)
      n_ref_copy++;
  }

  // do the data copies
  if (n_ref_copy) {
    for (i = 0; i < n_data; i++) {
      if ((*pass_type)[i] == ref_copy) {
        type = task->data_desc[i].type;
        size = task->data_desc[i].size;

        switch (type) {
        case inout: // input and output
          task->data_desc[i].ptr_l3_v = (void *)pulp_l3_malloc(pulp, size, (uintptr_t *)&(task->data_desc[i].ptr_l3_p));
          memcpy((void *)(task->data_desc[i].ptr_l3_v), (void *)(task->data_desc[i].ptr), size);
          break;

        case in: // input only
          task->data_desc[i].ptr_l3_v = (void *)pulp_l3_malloc(pulp, size, (uintptr_t *)&(task->data_desc[i].ptr_l3_p));
          memcpy((void *)(task->data_desc[i].ptr_l3_v), (void *)(task->data_desc[i].ptr), size);
          break;

        case out: // output only
          task->data_desc[i].ptr_l3_v = (void *)pulp_l3_malloc(pulp, size, (uintptr_t *)&(task->data_desc[i].ptr_l3_p));
          break;

        default:
          printf("ERROR: Invalid sh_mem_ctrl\n.");
          return -EINVAL;
        } // switch
      } // if
    } // for
  } // if

  return 0;
}

int pulp_offload_l3_copy_raw_in(PulpDev *pulp, const TaskDesc *task, const ElemPassType **pass_type)
{
  int i;
  unsigned n_ref_copy;
  int n_data;
  ElemType type;
  unsigned size;

  n_data = task->n_data;

  n_ref_copy = 0;

  // determine number of elements passed in which form
  for (i = 0; i < n_data; i++) {
    if ((*pass_type)[i] == ref_copy)
      n_ref_copy++;
  }

  // do the data copies
  if (n_ref_copy) {
    for (i = 0; i < n_data; i++) {
      if ((*pass_type)[i] == ref_copy) {
        type = task->data_desc[i].type;
        size = task->data_desc[i].size;

        switch (type) {
        case inout: // input and output
          memcpy((void *)(task->data_desc[i].ptr), (void *)(task->data_desc[i].ptr_l3_v), size);
          pulp_l3_free(pulp, (uintptr_t)(task->data_desc[i].ptr_l3_v), (uintptr_t)(task->data_desc[i].ptr_l3_p));
          break;

        case in: // input only
          pulp_l3_free(pulp, (uintptr_t)(task->data_desc[i].ptr_l3_v), (uintptr_t)(task->data_desc[i].ptr_l3_p));
          break;

        case out: // output only
          memcpy((void *)(task->data_desc[i].ptr), (void *)(task->data_desc[i].ptr_l3_v), size);
          pulp_l3_free(pulp, (uintptr_t)(task->data_desc[i].ptr_l3_v), (uintptr_t)(task->data_desc[i].ptr_l3_p));
          break;

        default:
          printf("ERROR: Invalid sh_mem_ctrl\n.");
          return -EINVAL;
        } // switch
      } // if
    } // for
  } // if

  return 0;
}

uintptr_t pulp_l3_malloc(PulpDev *pulp, unsigned size_b, uintptr_t *p_addr)
{
  if (DEBUG_LEVEL > 2) {
    printf("pulp_l3_malloc(%p, %d)\n", pulp, size_b);
  }

  // Align size of allocation to 8B because that's required by the PULP DMA.
  if (size_b & 0x7) {
    size_b = (size_b & ~0x7) + 0x8;
  }
  // The returned pointer is guaranteed to be aligned to a multiple of `sizeof(void*)`, which
  // fulfills the 8B alignment requirement of the PULP DMA.
  uintptr_t v_addr = (uintptr_t)o1heapAllocate((O1HeapInstance*)pulp->l3_heap_mgr, size_b);
  if (v_addr == 0) {
    return 0;
  }

  if (DEBUG_LEVEL > 2) {
    printf("Host virtual address = %#lx \n", v_addr);
  }

  // Calculate physical address.
  *p_addr = v_addr - (uintptr_t)pulp->l3_mem.v_addr + L3_MEM_BASE_ADDR;

  if (DEBUG_LEVEL > 2) {
    printf("PMCA physical address = %#lx \n", *p_addr);
  }

  return v_addr;
}

void pulp_l3_free(PulpDev *pulp, uintptr_t v_addr, uintptr_t p_addr)
{
  o1heapFree((O1HeapInstance*)pulp->l3_heap_mgr, (void*)v_addr);
}

int pulp_dma_xfer(const PulpDev *pulp, uintptr_t addr_l3, uintptr_t addr_pulp, size_t size_b, int host_read)
{
  unsigned request[3];

  // check & process arguments
  if (size_b >> 31) {
    printf("ERROR: Requested transfer size too large - cannot encode DMA transfer direction.\n ");
    return -EINVAL;
  } else if (host_read) {
    BF_SET(size_b, 1, 31, 1);
  }

  // setup the request
  request[0] = addr_l3;
  request[1] = addr_pulp;
  request[2] = size_b;

  // make the request
  ioctl(pulp->fd, PULP_IOCTL_DMA_XFER_ASYNC, request);

  return 0;
}

int pulp_omp_offload_task(PulpDev *pulp, TaskDesc *task)
{
  int err;

  // offload data
  err = pulp_offload_out(pulp, task);
  if (err) {
    printf("ERROR: Offloading data to PULP failed.\n");
    return err;
  }

  // load binary, boot PULP
  err = pulp_load_bin(pulp, task->name);
  if (err) {
    printf("ERROR: Load of PULP binary failed.\n");
    return err;
  }

  // start execution
  pulp_exe_start(pulp);

  return 0;
}
