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
#include <unistd.h>    // close(), sysconf()

#include <stdexcept>
#include <vector>

#include "aixlog.hpp"
#include "string_format.hpp"

class PhysMem {
 public:
  /** Map a physical memory region and make it accessible for reads and writes.

      \param  base_addr   Physical base address of the mapping; must be a multiple of the OS page
                          size
      \param  n_bytes     Number of bytes in the mapping

      Throws an `std::invalid_argument` exception if `base_addr` is not aligned to the OS page size.
      Throws an `std::runtime_error` exception if `/dev/mem` cannot be opened in read-write mode or
      if the call to `mmap()` fails.
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
  void write(const size_t phys_addr, const T value) {
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
  void write_u64(const size_t phys_addr, const uint64_t value) {
    this->write<uint64_t>(phys_addr, value);
  }

  /** Write an unsigned 32-bit value to a physical address in the mapped memory region.

      See `write()` member function for the documentation.
   */
  void write_u32(const size_t phys_addr, const uint32_t value) {
    this->write<uint32_t>(phys_addr, value);
  }

  /** Write an unsigned 16-bit value to a physical address in the mapped memory region.

      See `write()` member function for the documentation.
   */
  void write_u16(const size_t phys_addr, const uint16_t value) {
    this->write<uint16_t>(phys_addr, value);
  }

  /** Write an unsigned 8-bit value to a physical address in the mapped memory region.

      See `write()` member function for the documentation.
   */
  void write_u8(const size_t phys_addr, const uint8_t value) {
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

  /** Determine if a physical address range is entirely in the mapped memory region.

      \param  phys_addr   Physical address that is the start of the address range
      \param  n_bytes     Number of bytes in the address range
      \return             `true` if every address in the interval [phys_addr, phys_addr+n_bytes) is
                          in the mapped memory region; `false` otherwise.
   */
  bool maps_addr_range(const size_t phys_addr, const size_t n_bytes) const {
    return this->maps_addr(phys_addr) && this->maps_addr(phys_addr + n_bytes - 1);
  }

  /** Sets each byte in an address range to a given value.

      This function does *not* necessarily perform byte-wise stores!  In particular, this function
      may write multiple bytes at once if alignment and total number of bytes permit.

      \param  phys_addr   First physical address to write to
      \param  val         Byte value to write
      \param  n_bytes     Number of bytes that shall be written

      Throws an `std::invalid_argument` exception if an address in the interval
      [phys_addr, phys_addr+n_bytes) is not mapped.
    */
  void set(const size_t phys_addr, const uint8_t val, size_t n_bytes) {
    this->validate_addr_range(phys_addr, n_bytes);

    if (this->mock_only) {
      LOG(DEBUG) << "Would set";
    } else {
      LOG(DEBUG) << "Setting";
    }
    LOG(DEBUG) << " all bytes in address range "
               << string_format("[0x%p, 0x%p] to 0x%02x.", phys_addr, phys_addr + n_bytes - 1, val)
               << std::endl;

    // If this object only mocks physical memory accesses, return before the actual writes.
    if (this->mock_only) {
      return;
    }

    // If necessary, write a few bytes until the address is 64-bit aligned.
    volatile uint8_t* ptr = reinterpret_cast<volatile uint8_t*>(this->rel_ptr(phys_addr));
    while (reinterpret_cast<size_t>(ptr) % 8 != 0 && n_bytes > 0) {
      *ptr++ = val;
      n_bytes--;
    }
    // Then write as much as possible with 64-bit accesses.
    volatile uint64_t* ptr64 = reinterpret_cast<volatile uint64_t*>(ptr);
    while (n_bytes > 7) {
      *ptr64++ = u64_from_u8(val, val, val, val, val, val, val, val);
      n_bytes -= 8;
    }
    // Write remainder with 8-bit accesses.
    volatile uint8_t* ptr8 = reinterpret_cast<volatile uint8_t*>(ptr64);
    while (n_bytes > 0) {
      *ptr8++ = val;
      n_bytes--;
    }
  }

  /** Copy buffer to the physical memory region.

      \param  phys_addr   First physical address to write to.
      \param  src         Iterator into the source buffer.  This iterator must be able to provide
                          `n_bytes` bytes.  The iterator will be incremented `n_bytes-1` times, and
                          if it goes out of bounds during an increment, undefined behavior occurs.
      \param  n_bytes     Number of bytes to write.

      Throws an `std::invalid_argument` exception if an address in the interval
      [phys_addr, phys_addr+n_bytes) is not mapped.  When this exception is thrown, this function
      has not accessed the physical memory region.
   */
  void copy_to(const size_t phys_addr, std::vector<uint8_t>::const_iterator src, size_t n_bytes) {
    this->validate_addr_range(phys_addr, n_bytes);

    if (this->mock_only) {
      LOG(DEBUG) << "Would write";
    } else {
      LOG(DEBUG) << "Writing";
    }
    LOG(DEBUG) << " to address range "
               << string_format("[0x%p, 0x%p].", phys_addr, phys_addr + n_bytes - 1) << std::endl;

    // If this object only mocks physical memory accesses, return before the actual writes.
    if (this->mock_only) {
      return;
    }

    // If necessary, write a few bytes until the address is 64-bit aligned.
    volatile uint8_t* ptr = reinterpret_cast<volatile uint8_t*>(this->rel_ptr(phys_addr));
    while (reinterpret_cast<size_t>(ptr) % 8 != 0 && n_bytes > 0) {
      *ptr++ = *src++;
      n_bytes--;
    }
    // Then write as much as possible with 64-bit accesses.
    volatile uint64_t* ptr64 = reinterpret_cast<volatile uint64_t*>(ptr);
    while (n_bytes > 7) {
      *ptr64++ = u64_from_u8(*src++, *src++, *src++, *src++, *src++, *src++, *src++, *src++);
      n_bytes -= 8;
    }
    // Write remainder with 8-bit accesses.
    volatile uint8_t* ptr8 = reinterpret_cast<volatile uint8_t*>(ptr64);
    while (n_bytes > 0) {
      *ptr8++ = *src++;
      n_bytes--;
    }
  }

  /** Copy from the physical memory region into a buffer.

      \param  phys_addr   First physical address to read from.
      \param  dst         Destination buffer.  This function reserves `n_bytes` in this
                          `std::vector`, so a pre-reservation is not necessary.
      \param  n_bytes     Number of bytes to read.

      Throws an `std::invalid_argument` exception if an address in the interval
      [phys_addr, phys_addr+n_bytes) is not mapped.  When this exception is thrown, this function
      has not accessed the physical memory region and has not reserved capacity in `dst`.
   */
  void copy_from(const size_t phys_addr, std::vector<uint8_t>& dst, size_t n_bytes) const {
    this->validate_addr_range(phys_addr, n_bytes);

    if (this->mock_only) {
      LOG(DEBUG) << "Would read";
    } else {
      LOG(DEBUG) << "Reading";
    }
    LOG(DEBUG) << " from address range "
               << string_format("[0x%p, 0x%p].", phys_addr, phys_addr + n_bytes - 1) << std::endl;

    // Reserve memory in destination buffer.
    dst.reserve(n_bytes);

    // If this object only mocks physical memory accesses, return before the actual reads.
    if (this->mock_only) {
      return;
    }

    // If necessary, read a few bytes until the address is 64-bit aligned.
    const volatile uint8_t* ptr =
        reinterpret_cast<const volatile uint8_t*>(this->rel_ptr(phys_addr));
    while (reinterpret_cast<size_t>(ptr) % 8 != 0 && n_bytes > 0) {
      dst.push_back(static_cast<uint8_t>(*ptr++));
      n_bytes--;
    }
    // Then read as much as possible with 64-bit accesses.
    const volatile uint64_t* ptr64 = reinterpret_cast<const volatile uint64_t*>(ptr);
    while (n_bytes > 7) {
      const uint64_t val = *ptr64++;
      dst.push_back((val >> 0) & 0xFF);
      dst.push_back((val >> 8) & 0xFF);
      dst.push_back((val >> 16) & 0xFF);
      dst.push_back((val >> 24) & 0xFF);
      dst.push_back((val >> 32) & 0xFF);
      dst.push_back((val >> 40) & 0xFF);
      dst.push_back((val >> 48) & 0xFF);
      dst.push_back((val >> 56) & 0xFF);
      n_bytes -= 8;
    }
    // Read remainder with 8-bit accesses.
    const volatile uint8_t* ptr8 = reinterpret_cast<const volatile uint8_t*>(ptr64);
    while (n_bytes > 0) {
      dst.push_back(static_cast<uint8_t>(*ptr8++));
      n_bytes--;
    }
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

    // Ensure that base address is a multiple of the OS page size.
    const size_t page_size = sysconf(_SC_PAGE_SIZE);
    if (base_addr % page_size != 0) {
      throw std::invalid_argument(string_format(
          "'base_addr' (%p) is not aligned with OS page size (%d B)", base_addr, page_size));
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
  inline volatile void* rel_ptr(const size_t phys_addr) const {
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
  inline void validate_addr(const size_t phys_addr) const {
    if (!this->maps_addr(phys_addr)) {
      throw std::invalid_argument(string_format("Address %p is not mapped!", phys_addr));
    }
  }

  /** Validate that a physical address range is in the mapped memory region.

      Throws an `std::invalid_argument` exception if that is not the case.
   */
  inline void validate_addr_range(const size_t phys_addr, const size_t n_bytes) const {
    if (!this->maps_addr_range(phys_addr, n_bytes)) {
      throw std::invalid_argument(
          string_format("Address range [%p,%p) is not mapped!", phys_addr, phys_addr + n_bytes));
    }
  }

  static inline uint64_t u64_from_u8(const uint8_t byte0, const uint8_t byte1, const uint8_t byte2,
                                     const uint8_t byte3, const uint8_t byte4, const uint8_t byte5,
                                     const uint8_t byte6, const uint8_t byte7) {
    return (static_cast<uint64_t>(byte0) << 0) | (static_cast<uint64_t>(byte1) << 8) |
           (static_cast<uint64_t>(byte2) << 16) | (static_cast<uint64_t>(byte3) << 24) |
           (static_cast<uint64_t>(byte4) << 32) | (static_cast<uint64_t>(byte5) << 40) |
           (static_cast<uint64_t>(byte6) << 48) | (static_cast<uint64_t>(byte7) << 56);
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
