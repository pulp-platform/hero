# PULP Linux Kernel Driver

This driver interfaces PULP in Linux as a device.  It handles initialization and clearing of
hardware registers, allocation and deallocation of kernel objects, provides memory-mapped access to
parts of the hardware, implements IOCTL callbacks from user space, handles interrupts coming from
PULP, provides an interface to the device tree, manages virtual memory between host and PULP.

This document gives an overview of the driver.  The API and its implementation are documented with
Doxygen headers in the code.

The driver is organized into source and header files as follows:
- `pulp_module` is the root file of the driver, which implements
  - the `init` function, which is executed when Linux loads the driver
  - the `exit` function, which is executed when Linux unloads the driver
  - the `open` function, which is executed when the device is opened
  - the `release` function, which is executed when the device is closed
  - the `mmap` function, which maps parts of the hardware to virtual memory
  - the `isr` function, which services interrupts from PULP
  - the `ioctl` function, which reads and/or writes control logic in the hardware on IOCTL calls
  - the device tree interface
  - the SysFS interface
- `pulp_ctrl` implements reset and clock frequency control of PULP on different platforms.
- `pulp_dma` implements host-side DMA transfers from and to PULP memory.
- `pulp_mbox` implements reads, writes, control, and interrupts of the mailbox used to communicate
  with PULP.
- `pulp_mem` implements memory interfaces to PULP:
  - cache flushing and invalidations
  - segmented memory maps
  - `get_user_pages`
- `pulp_profile` implements profiling infrastructure (counters, timers) for PULP.
- `pulp_rab` implements control and run-time management to use PULP together with the 'RAB' IOMMU.
- `pulp_smmu` implements control and run-time management to use PULP together with an ARM SMMU.
