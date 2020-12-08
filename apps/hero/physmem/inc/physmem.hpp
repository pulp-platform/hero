/** Copyright (c) 2020 ETH Zurich, University of Bologna
 *  SPDX-License-Identifier: Apache-2.0
 *
 *  Header-Only Library for Physical Memory Accessing on Linux
 *
 *  Author: Andreas Kurth <akurth@iis.ee.ethz.ch>
 */

#include <fcntl.h>     // open()
#include <sys/mman.h>  // mmap(), munmap()
#include <unistd.h>    // close()

#include <stdexcept>

#include "aixlog.hpp"
#include "string_format.hpp"

class PhysMem {
 public:
  /** Map a physical memory region and make it accessible for reads and writes.

      \param  base_addr   Physical base address of the mapping
      \param  n_bytes     Number of bytes in the mapping
   */
  PhysMem(const size_t base_addr, const size_t n_bytes) {
    // Initialize logging library.  This should actually not be done in the constructor, because
    // creating two `PhysMem` objects now probably corrupts logging.  However, if `AixLog` is not
    // initialized at all, it unconditionally prints every message and does not format them
    // properly.  So we would burden the user to initialize the logging library for using this
    // class, which is unintuitive as well.  Maybe this should be replaced by a better header-only
    // logging library; but I know none.
    //
    // To increase logging verbosity, change to `AixLog::Severity::debug` or lower.
    AixLog::Log::init<AixLog::SinkCerr>(AixLog::Severity::warning);

    // Open a file descriptor into `/dev/mem`.
    this->fd = open("/dev/mem", O_RDWR | O_SYNC);
    if (this->fd == -1) {
      throw std::runtime_error("Could not open '/dev/mem'!");
    }
    LOG(DEBUG) << "Opened '/dev/mem' with fd=" << this->fd << "." << std::endl;

    // Map the specified physical memory region.
    this->base_addr = base_addr;
    this->n_bytes = n_bytes;
    this->map_mask = this->n_bytes - 1;
    this->map_ptr = mmap(0, this->n_bytes, PROT_READ | PROT_WRITE, MAP_SHARED, fd,
                         this->base_addr & ~this->map_mask);
    if (this->map_ptr == (void*)-1) {
      throw std::runtime_error("'mmap' failed!");
    }
    LOG(DEBUG) << "Memory mapped at address " << const_cast<void*>(this->map_ptr) << "."
               << std::endl;
  };

  ~PhysMem() {
    const int res = munmap((void*)this->map_ptr, this->n_bytes);
    LOG(DEBUG) << "Unmapped memory." << std::endl;
    if (res == -1) {
      LOG(ERROR) << "'munmap' failed!" << std::endl;
    }
    close(this->fd);
    LOG(DEBUG) << "Closed '/dev/mem'." << std::endl;
  }

  /** Read a unsigned 32-bit value from a physical address in the mapped memory region.

      \param  phys_addr   Physical address to be read from
      \return             The read value.

      Throws an `std::invalid_argument` exception if `phys_addr` is not in the mapped memory
      region.
   */
  uint32_t read_u32(const size_t phys_addr) {
    this->validate_addr(phys_addr);
    LOG(DEBUG) << "Reading from 0x" << std::hex << phys_addr << "." << std::endl;
    const uint32_t value = *(volatile uint32_t*)this->rel_ptr(phys_addr);
    LOG(DEBUG) << "Read 0x" << std::hex << value << "." << std::endl;
    return value;
  }

  /** Write a unsigned 32-bit value to a physical address in the mapped memory region.

      \param  phys_addr   Physical address to be written to
      \param  value       Value to write

      Throws an `std::invalid_argument` exception if `phys_addr` is not in the mapped memory region.
   */
  void write_u32(const size_t phys_addr, const uint32_t value) {
    this->validate_addr(phys_addr);
    LOG(DEBUG) << "Writing " << value << " to " << phys_addr << "." << std::endl;
    *(volatile uint32_t*)this->rel_ptr(phys_addr) = value;
  }

  /** Determine if a physical address is in the mapped memory region.

      \param  phys_addr   Physical address
      \return             `true` if `phys_addr` is in the mapped memory region;
                          `false` if it is not.
   */
  bool maps_addr(const size_t phys_addr) {
    return phys_addr >= this->base_addr && phys_addr < base_addr + n_bytes;
  }

 private:
  /** The file descriptor returned by `open`. */
  int fd;
  /** The `base_addr` and `n_bytes` given to the constructor. */
  size_t base_addr, n_bytes;
  /** Bitmask that selects the LSBs within `n_bytes`. */
  size_t map_mask;
  /** The pointer returned by `mmap`. */
  volatile void* map_ptr;

  /** Get relative pointer in the virtual address space that can be used to access a physical
      address.

      \param  phys_addr   Physical address
      \return             Virtual address pointer that corresponds to the physical address.
    */
  volatile void* rel_ptr(const size_t phys_addr) {
    return (volatile void*)((size_t)this->map_ptr + (phys_addr & this->map_mask));
  }

  /** Validate that a physical address is in the mapped memory region.

      Throws an `std::invalid_argument` exception if that is not the case.
   */
  void validate_addr(const size_t phys_addr) {
    if (!this->maps_addr(phys_addr)) {
      throw std::invalid_argument(string_format("Address %p is not mapped!", phys_addr));
    }
  }
};
