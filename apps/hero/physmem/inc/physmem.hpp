/** Copyright (c) 2020 ETH Zurich, University of Bologna
 *  SPDX-License-Identifier: Apache-2.0
 *
 *  Header-Only Library for Physical Memory Accessing on Linux
 *
 *  Author: Andreas Kurth <akurth@iis.ee.ethz.ch>
 */

#ifndef HERO_PHYSMEM_H_
#define HERO_PHYSMEM_H_

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
  PhysMem(const size_t base_addr, const size_t n_bytes)
      : PhysMem(base_addr, n_bytes, false){
            // Delegate implementation to protected constructor (see below) with `mock_only`
            // argument set to `false`.
        };

  ~PhysMem() {
    // If this object only mocked physical memory accesses, the destructor has nothing to do.
    if (this->mock_only) {
      return;
    }

    const int res = munmap(const_cast<void*>(this->map_ptr), this->n_bytes);
    LOG(DEBUG) << "Unmapped memory." << std::endl;
    if (res == -1) {
      LOG(ERROR) << "'munmap' failed!" << std::endl;
    }
    close(this->fd);
    LOG(DEBUG) << "Closed '/dev/mem'." << std::endl;
  }

  /** Read from a physical address in the mapped memory region.

      \param  phys_addr   Physical address to be read from
      \return             The read value.

      Throws an `std::invalid_argument` exception if `phys_addr` is not in the mapped memory
      region.
   */
  template <typename T>
  T read(const size_t phys_addr) const {
    this->validate_addr(phys_addr);

    if (this->mock_only) {
      LOG(DEBUG) << "Would read";
    } else {
      LOG(DEBUG) << "Reading";
    }
    LOG(DEBUG) << " from 0x" << std::hex << phys_addr << "." << std::endl;

    // If this object only mocks physical memory accesses, return before the actual read.
    if (this->mock_only) {
      return 0;
    }

    const T value = *reinterpret_cast<volatile T*>(this->rel_ptr(phys_addr));
    LOG(DEBUG) << "Read 0x" << std::hex << static_cast<unsigned long>(value) << "." << std::endl;
    return value;
  }

  /** Read an unsigned 64-bit value from a physical address in the mapped memory region.

      See `read()` member function for the documentation.
   */
  uint64_t read_u64(const size_t phys_addr) const { return this->read<uint64_t>(phys_addr); }

  /** Read an unsigned 32-bit value from a physical address in the mapped memory region.

      See `read()` member function for the documentation.
   */
  uint32_t read_u32(const size_t phys_addr) const { return this->read<uint32_t>(phys_addr); }

  /** Read an unsigned 16-bit value from a physical address in the mapped memory region.

      See `read()` member function for the documentation.
   */
  uint16_t read_u16(const size_t phys_addr) const { return this->read<uint16_t>(phys_addr); }

  /** Read an unsigned 8-bit value from a physical address in the mapped memory region.

      See `read()` member function for the documentation.
   */
  uint8_t read_u8(const size_t phys_addr) const { return this->read<uint8_t>(phys_addr); }

  /** Write to a physical address in the mapped memory region.

      \param  phys_addr   Physical address to be written to
      \param  value       Value to write

      Throws an `std::invalid_argument` exception if `phys_addr` is not in the mapped memory region.
   */
  template <typename T>
  void write(const size_t phys_addr, const T value) const {
    this->validate_addr(phys_addr);

    if (this->mock_only) {
      LOG(DEBUG) << "Would write";
    } else {
      LOG(DEBUG) << "Writing";
    }
    LOG(DEBUG) << " 0x" << std::hex << static_cast<unsigned long>(value) << " to 0x" << phys_addr
               << "." << std::endl;

    // If this object only mocks physical memory accesses, return before the actual write.
    if (this->mock_only) {
      return;
    }

    *reinterpret_cast<volatile T*>(this->rel_ptr(phys_addr)) = value;
  }

  /** Write an unsigned 64-bit value to a physical address in the mapped memory region.

      See `write()` member function for the documentation.
   */
  void write_u64(const size_t phys_addr, const uint64_t value) const {
    this->write<uint64_t>(phys_addr, value);
  }

  /** Write an unsigned 32-bit value to a physical address in the mapped memory region.

      See `write()` member function for the documentation.
   */
  void write_u32(const size_t phys_addr, const uint32_t value) const {
    this->write<uint32_t>(phys_addr, value);
  }

  /** Write an unsigned 16-bit value to a physical address in the mapped memory region.

      See `write()` member function for the documentation.
   */
  void write_u16(const size_t phys_addr, const uint16_t value) const {
    this->write<uint16_t>(phys_addr, value);
  }

  /** Write an unsigned 8-bit value to a physical address in the mapped memory region.

      See `write()` member function for the documentation.
   */
  void write_u8(const size_t phys_addr, const uint8_t value) const {
    this->write<uint8_t>(phys_addr, value);
  }

  /** Determine if a physical address is in the mapped memory region.

      \param  phys_addr   Physical address
      \return             `true` if `phys_addr` is in the mapped memory region;
                          `false` if it is not.
   */
  bool maps_addr(const size_t phys_addr) const {
    return (phys_addr >= this->base_addr) && (phys_addr < this->base_addr + this->n_bytes);
  }

 protected:
  /** Internal constructor of a physical memory mapping.  This contains the actual constructor
      implementation and takes the following parameter in addition to the public `PhysMem`
      constructor:

      \param  mock_only   Whether this only mocks a physical memory mapping (see documentation of
                          `MockPhysMem` for details).
   */
  PhysMem(const size_t base_addr, const size_t n_bytes, const bool mock_only)
      : base_addr(base_addr), n_bytes(n_bytes), map_mask(n_bytes - 1), mock_only(mock_only) {
    // Initialize logging library.  This should actually not be done in the constructor, because
    // creating two `PhysMem` objects now probably corrupts logging.  However, if `AixLog` is not
    // initialized at all, it unconditionally prints every message and does not format them
    // properly.  So we would burden the user to initialize the logging library for using this
    // class, which is unintuitive as well.  Maybe this should be replaced by a better header-only
    // logging library; but I know none.
    //
    // To increase logging verbosity, change to `AixLog::Severity::debug` or lower.
    if (mock_only) {
      AixLog::Log::init<AixLog::SinkCerr>(AixLog::Severity::debug);
    } else {
      AixLog::Log::init<AixLog::SinkCerr>(AixLog::Severity::warning);
    }

    // If this object only mocks physical memory accesses, print an info message and exit the
    // constructor early.
    if (mock_only) {
      LOG(INFO) << "Mock-only PhysMem.  Would map 0x" << std::hex << n_bytes
                << " bytes starting at 0x" << base_addr << "." << std::endl;
      return;
    }

    // Open a file descriptor into `/dev/mem`.
    this->fd = open("/dev/mem", O_RDWR | O_SYNC);
    if (this->fd == -1) {
      throw std::runtime_error("Could not open '/dev/mem'!");
    }
    LOG(DEBUG) << "Opened '/dev/mem' with fd=" << this->fd << "." << std::endl;

    // Map the specified physical memory region.
    this->map_ptr = mmap(0, this->n_bytes, PROT_READ | PROT_WRITE, MAP_SHARED, fd,
                         this->base_addr & ~this->map_mask);
    if (this->map_ptr == reinterpret_cast<void*>(-1)) {
      throw std::runtime_error("'mmap' failed!");
    }
    LOG(DEBUG) << "Memory mapped at address " << const_cast<void*>(this->map_ptr) << "."
               << std::endl;
  };

 private:
  /** The file descriptor returned by `open`. */
  int fd;
  /** The `base_addr` and `n_bytes` given to the constructor. */
  const size_t base_addr, n_bytes;
  /** Bitmask that selects the LSBs within `n_bytes`. */
  const size_t map_mask;
  /** The pointer returned by `mmap`. */
  volatile void* map_ptr;
  /** Whether this object only mocks physical memory accesses. */
  const bool mock_only;

  /** Get relative pointer in the virtual address space that can be used to access a physical
      address.

      \param  phys_addr   Physical address
      \return             Virtual address pointer that corresponds to the physical address.
    */
  volatile void* rel_ptr(const size_t phys_addr) const {
    if (this->mock_only) {
      throw std::runtime_error("method undefined for mock PhysMem");
    }
    const size_t offset = phys_addr & this->map_mask;
    const size_t rel_addr = reinterpret_cast<size_t>(this->map_ptr) + offset;
    return reinterpret_cast<volatile void*>(rel_addr);
  }

  /** Validate that a physical address is in the mapped memory region.

      Throws an `std::invalid_argument` exception if that is not the case.
   */
  void validate_addr(const size_t phys_addr) const {
    if (!this->maps_addr(phys_addr)) {
      throw std::invalid_argument(string_format("Address %p is not mapped!", phys_addr));
    }
  }
};

class MockPhysMem : public PhysMem {
 public:
  /** Mock mapping a physical memory region.  This does *not* map or access any physical memory, but
      it prints the addresses of all calls to the `read()` and `write()` member functions.  This can
      be useful for the validation of a program that accesses physical memory without risking any
      memory corruption or undesired side effects.

      - This class inherits the entire public API from `PhysMem`, so it is documented there.
      - `write()` additionally prints the value that would be written.
      - `read()` always returns `0` and does not print a value (since the value that would be read
        is obviously unknown).
   */
  MockPhysMem(const size_t base_addr, const size_t n_bytes) : PhysMem(base_addr, n_bytes, true){};
};

#endif  // HERO_PHYSMEM_H_
