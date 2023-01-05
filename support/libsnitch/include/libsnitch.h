#pragma once

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <unistd.h> // for useconds_t

#include "snitch_module.h"

typedef struct {
  void *v_addr;
  void *p_addr;
  unsigned size;
} SnitchSubDev;

enum log_level {
  LOG_ERROR = 0,
  LOG_WARN = 1,
  LOG_INFO = 2,
  LOG_DEBUG = 3,
  LOG_TRACE = 4,
  LOG_MIN = LOG_ERROR,
  LOG_MAX = LOG_TRACE,
};

// Must be same as in snRuntime
struct BootData {
  uint32_t boot_addr;
  uint32_t core_count;
  uint32_t hartid_base;
  uint32_t tcdm_start;
  uint32_t tcdm_size;
  uint32_t tcdm_offset;
  uint64_t global_mem_start;
  uint64_t global_mem_end;
  uint32_t cluster_count;
  uint32_t s1_quadrant_count;
  uint32_t clint_base;
};

typedef struct {
  int fd; // file descriptor
  struct sn_cluster_info sci;
  SnitchSubDev l1;
  SnitchSubDev periph;
  SnitchSubDev l3;
  struct O1HeapInstance *l3_heap_mgr;
  // offset in l3 memory where shared data region starts and the o1heap manager is allocating
  uint64_t l3_data_offset;
  // L3 layout structure, private to each cluster
  struct l3_layout *l3l;
  // Physical address of l3_layout data
  void *l3l_p;
  volatile struct ring_buf *a2h_mbox;
  volatile struct ring_buf *h2a_mbox;
} snitch_dev_t;

/**
 * Values read from snitch cluster peripheral
 */
typedef struct {
  uint32_t tcdmStartAddress;
  uint32_t tcdmEndAddress;
  uint32_t nrCores;
  uint32_t fetchEnable;
  uint64_t scratch;
  uint64_t cycle;
  uint32_t barrier;
  uint32_t hartBaseID;
  uint32_t tcdmAccessed;
  uint32_t tcdmCongested;
  uint32_t *counters;
} snitch_perf_t;

/*  ____        _ _       _          _    ____ ___
 * / ___| _ __ (_) |_ ___| |__      / \  |  _ \_ _|
 * \___ \| '_ \| | __/ __| '_ \    / _ \ | |_) | |
 *  ___) | | | | | || (__| | | |  / ___ \|  __/| |
 * |____/|_| |_|_|\__\___|_| |_| /_/   \_\_|  |___|
 */

/**
 * @brief Set the log level accoring to `ll`
 *
 * @param dev pointer to snitch struct
 * @param ll log levl
 */
void snitch_set_log_level(enum log_level ll);

/**
 * @brief Discover snitch clusters by globbing /dev/snitch* and probing each device
 * @param devs if not NULL, a list of strings to the discovered devices it put in *devs
 * @param cluster if not NULL, number of clusters written to
 * @param quadrants if not NULL, number of quadrants written to
 *
 * @return int negative error or number of clusters discovered
 */
int snitch_discover(char ***devs, uint32_t *clusters, uint32_t *quadrants);

/**
 * @brief Memory-map all snitch clusters in the system to user-space
 * @param nr_dev [out] number of devices mapped
 *
 * @return snitch_dev_t** array of pointers to snitch cluster devices
 */
snitch_dev_t **snitch_mmap_all(uint32_t *nr_dev);

/**
 * @brief Map the snitch device to virtual user space using mmap syscall to the snitch driver
 * @details
 *
 * @param dev pointer to snitch struct
 * @param fname path to the char device (e.g. /dev/snitch1)
 * @return 0 on success, negative and errno on fault
 */
int snitch_mmap(snitch_dev_t *dev, char *fname);

/**
 * @brief Flush all data caches
 * @details
 *
 * @param dev pointer to snitch struct
 * @return 0 on success, negative and errno on fault
 */
int snitch_flush(snitch_dev_t *dev);

/**
 * @brief Perform hardware reset of all components. Clusters are trapped in bootrom after this and
 * wait for interrupt
 * @details
 *
 * @param dev pointer to snitch device structure
 *
 * @return 0 on success
 */
int snitch_reset(snitch_dev_t *dev);

/**
 * @brief Load snitch binary to L3
 *
 * @param dev pointer to snitch struct
 * @param name file name
 *
 * @return binary size in bytes on success, negative errno on error
 */
int snitch_load_bin(snitch_dev_t *dev, const char *name);

/**
 * @brief Set isolation of snitch cluster. Forwarded to driver. Isolate waits for isolated and then
 * puts cluster in reset. Deisolation releases from reset and clears isolateion. Return can be
 * -ETIMEOUT if isolated response not received
 * @details
 *
 * @param dev pointer to snitch struct
 * @param iso 1 to isolate, 0 to de-isolate
 * @return 0 on success, negative ERRNO on failure
 */
int snitch_isolate(snitch_dev_t *dev, int iso);

/**
 * @brief Write to a SoC scratch register
 *
 * @param dev pointer to snitch struct
 * @param reg register offset in words
 * @param val value to write to
 * @return int return value of the ioctl call, 0 on success, negative error on failure
 */
int snitch_scratch_reg_write(snitch_dev_t *dev, uint32_t reg, uint32_t val);

/**
 * @brief Read from a SoC scratch register
 *
 * @param dev pointer to snitch struct
 * @param reg register offset in words
 * @param val value that was read
 * @return int return value of the ioctl call, 0 on success, negative error on failure
 */
int snitch_scratch_reg_read(snitch_dev_t *dev, uint32_t reg, uint32_t *val);

/**
 * @brief Set bits in the CLINT SW interrupt registers
 *
 * @param dev pointer to snitch struct
 * @param reg CLINT register offset
 * @param mask mask of bits to set
 * @return int return value of the ioctl call, 0 on success, negative error on failure
 */
int snitch_ipi_set(snitch_dev_t *dev, uint32_t reg, uint32_t mask);

/**
 * @brief Clear bits in the CLINT SW interrupt registers
 *
 * @param dev pointer to snitch struct
 * @param reg CLINT register offset
 * @param mask mask of bits to clear
 * @return int return value of the ioctl call, 0 on success, negative error on failure
 */
int snitch_ipi_clear(snitch_dev_t *dev, uint32_t reg, uint32_t mask);

/**
 * @brief Read bits from CLINT SW interrupt registers
 *
 * @param dev pointer to snitch struct
 * @param reg CLINT register offset
 * @param mask register value is written to *mask
 * @return int return value of the ioctl call, 0 on success, negative error on failure
 */
int snitch_ipi_get(snitch_dev_t *dev, uint32_t reg, uint32_t *mask);

/** Allocate a chunk of memory in contiguous L3.

  \param    dev   pointer to the snitch_dev_t structure
  \param    size size in Bytes of the requested chunk
  \param    p_addr pointer to store the physical address to

  \return   virtual user-space address for host
 */
void *snitch_l3_malloc(snitch_dev_t *dev, size_t size, void **p_addr);

/** Free memory previously allocated in contiguous L3.

 \param    dev   pointer to the snitch_dev_t structure
 \param    v_addr pointer to unsigned containing the virtual address
 \param    p_addr pointer to unsigned containing the physical address

 */
void snitch_l3_free(snitch_dev_t *dev, void *v_addr, void *p_addr);

/** Read one or multiple words from the mailbox. Blocks if the mailbox does not contain enough
 *  data.

 \param    dev   pointer to the snitch_dev_t structure
  \param    buffer  pointer to read buffer
  \param    n_words number of words to read

  \return   0 on success; negative value with an errno on errors.
 */
int snitch_mbox_read(const snitch_dev_t *dev, uint32_t *buffer, size_t n_words);

/**
 * @brief Try to read from the mailbox. On success, message is written to buffer and 1 is returned.
 * If no element is present, 0 is returned
 *
 * @param dev pointer to the snitch_dev_t structure
 * @param buffer pointer to the buffer where the message word is stores
 * @return int 0 if no message was received, 1 if message was received and written to buffer
 */
int snitch_mbox_try_read(const snitch_dev_t *dev, uint32_t *buffer);

/** Write one word to the mailbox. Blocks if the mailbox is full.

 \param    dev   pointer to the snitch_dev_t structure
 \param     word word to write

 \return    0 on success; negative value with an errno on errors.
 */
int snitch_mbox_write(snitch_dev_t *dev, uint32_t word);

/**
 * @brief Write to a TLB entry
 *
 * @param    dev   pointer to the snitch_dev_t structure
 * @param    e     the TLB entry
 * @return int errno return code
 */
int snitch_tlb_write(snitch_dev_t *dev, struct axi_tlb_entry *e);

/**
 * @brief Read a TLB entry
 *
 * @param    dev   pointer to the snitch_dev_t structure
 * @param    e     the TLB entry
 * @return int errno return code
 */
int snitch_tlb_read(snitch_dev_t *dev, struct axi_tlb_entry *e);

/**
 * @brief Set device log level through mailboxes.
 *
 * @param dev   pointer to the snitch_dev_t structure
 * @param lvl   new log level or -1 to read it from the SNITCH_DEBUG environment variable
 */
void snitch_set_device_loglevel(snitch_dev_t *dev, int lvl);

int snitch_test_read_regions(snitch_dev_t *dev, uint32_t reg);


//!@}
