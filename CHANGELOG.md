# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).


## Unreleased

### Added
- Clang/LLVM: Add full support for the `Xpulpv2` ISA extension, including intrinsics for
  compatibility with PULP GCC.  This has been partially contributed by University of Tuebingen.

### Changed
- Clang/LLVM:
  - Update from 9.0.1 to 12.0.1.
  - Deprecate the use of configurable host/device address spaces.  The native address space is now
    always AS 0, and the wider address space is AS 1.  This addresses issue #105, enabling better
    integration with statistics and aligns with upstream (to enable the update to LLVM 12).
  - Join repository with the Snitch and Mempool projects to simplify exchange of common fixes.
- Buildroot: Update from 2019.02.1 to 2021.02.3 to bring tools such as CMAKE to a version compatible
  with LLVM 12.  This also allows to set the `CC` and `CXX` environment variables when building
  `tc-llvm`, in case the default compiler on the system is too old.
- `br-hrv-eqemu`: Use OpenSBI instead of RISC-V PK as bootloader, because the latter has been
  deprecated in Buildroot.
- PREM passes (HC-p):
  - Data that already resides in L1 is not copied to the PREM buffer in L1, only data in L2 and L3
    are now copied.
  - Messages about HERCULES PREM passes are now being printed only if they are active, whereas
    previously those messages were printed if they were *not* active.

### Fixed
- Clang/LLVM:
  - Optimize the usage of the `Xpulpv2` instructions that were already supported (post-increment and
    hardware loops) to significantly improve performance of generated code.
  - Fix issue with post-increment that caused the OpenMP `for` worksharing construct with `dynamic`
    schedule to fail.
- PREM passes (HC-p):
  - Improve address space awareness in PREM passes to solve issues with 64-bit pointers on PULP.
  - Fix various bugs in the AutoDMA/PREM passes.


## v0.2.1 - 2021-04-15

### Added
- PULP DMA engine: Add support for 64-bit external addresses.

### Changed
- PREM support is now activated with `make prem-set` at the beginning of the HERO setup.  This
  replaces the previous configuration where special make-targets with a `-prem` suffix were used.

### Fixed
- Clang/LLVM:
  - Fix truncation of 64-bit addresses when compiling with `only=pulp` address spaces (!243).
  - Fix persistence of `xpulpv2` feature flag in RISC-V backend (!252).
- `prem-cmux` Buildroot package: Add missing commands for installing into target directory.
- `toolchain/HerculesCompiler-public` (!247):
  - Fix several bugs where OpenMP variables (`iv`, `lb`, `ub`, `stride`) would cause failures during
    scalar evolution loop analysis.
  - Several OpenMP runtime functions (notably `static_init`) are now treated as external symbols,
    handled in compatible intervals.  This prevents crashes in nested `parallel for` regions.
  - Remove unmaintained multi-cluster support for PREM offloading with OpenMP (CMUX VOTE).  The new
    implementation is instead leaner and better optimized for single cluster offloading.
  - Remove the artifact compatible interval with major ID `INT_MAX`, previously generated at the
    beginning of each program entry point.  This interval was there for legacy reasons and not
    reported by the compiler.
  - CMUX now includes `cmuxperf` make target, which builds a CMUX version that traces and dumps
    statistics about PREMized binaries.  Not built by default by the `prem-cmux` Buildroot package.
  - The `HERCULES_QUIET` environment variable now suppresses more non-expert output.
  - Add `HERCULES_GLOBAL_INTERVAL_IDS` environment variable that allows PREM interval numbering to
    be unique over several compilation units.
- Hardware -> RI5CY/CV32E40P core: Fix cancelling of ALU operation after taken branch (!253).  Prior
  to this fix, ALU instructions following a taken branch would not be cancelled properly, causing a
  delay up to the full number of cycles taken to execute the instruction (which can be >30 for
  division and remainder instructions).


## v0.2.0 - 2021-03-18

### Added
- `libhero-target`:
  - Add `hero_perf_*` performance measurement API.  This API provides a uniform interface for
    counting events on different devices, does not require all events to be supported on every
    device, and works with hardware counters dynamically assigned an to event as well as with
    hardware counters statically bound ("hardwired") to an event.  See !223 for details.
  - Add two-dimensional memory copy functions (`hero_memcpy2d_*`).
- Benchmarks and example applications:
  - Add benchmark (`openmp-examples/dma-perf`) to measure DMA throughput and verify the correctness
    of transferred data for different transfer sizes and source and destination memory alignments.
  - Add TinyYOLOv3 (`openmp-examples/darknet`) as a benchmark, with the convolution layers ported to
    run on PULP.  This also comes with a reduced version (`openmp-examples/darknet-layer`), which
    executes a single convolutional layer at a time, checks correctness and then exits.
- Add support for the Predictable Execution Model (PREM) from the HERCULES PREMizing compiler.
  Activate it with `export HERCULES_INSTALL=$HERO_INSTALL` before sourcing the `exilzcu102.sh`
  environment file (this is the only setup currently supported).  The environment script has been
  extended to also configure the toolchain for PREM transformation.  To build the required runtime
  libraries, build the target `sdk-har-prem` instead of `sdk-har`, but otherwise follow instructions
  as previously.
- Add `util/devrebuild`: programs to rebuild (and optionally redeploy) components of the HERO SDK
  during development.

### Changed
- Hardware:
  - Replace RAB by AXI TLB.  This fixes the DMA burst size limitation due to a bug in the RAB (#84).
  - RI5CY/CV32E40P core: Replace PULP-custom hardware counters with RISC-V standard Hardware
    Performance Monitor (currently parametrized to two dynamically assignable hardware counters).
  - Replace `mchan` DMA engine by AXI DMA engine.  This significantly improves the throughput of DMA
    transfers (see !216 for details).
- Clang verbosity: Clang by default no longer prints notices to `stderr` on custom address space
  handling decisions, because these obscure compiler warnings that are more useful to the end user.
  Instead, the `HERO_VERBOSITY` environment variable has been added to control the verbosity.  The
  verbosity levels go from `0` (meaning "only print emergency messages") to 7 (meaning "print all
  debug messages").  To re-enable the previous behavior, set `HERO_VERBOSITY` to `5` or higher.
- Rename folder containing development machine utilities from `tools` to `util`.

### Fixed
- Hardware: Fix decoding of 64-bit addresses in PULP's cluster bus.  Previously, addresses outside
  the 32-bit range would lead to a decode error in the cluster bus.

### Removed
- `libhero-target`: Remove `hero_reset_clk_counter()`, thereby making the clock counter
  non-resettable and thus monotonically increasing.  The monotonicity property is important so that
  different usages of the cycle counter do not interfere.


## v0.1.4 - 2021-02-10

### Added
- PULP runtime: Add a simple heap overflow protection mechanism (with very low runtime overhead).

### Changed
- Hardware:
  - RI5CY/CV32E40P core: Remove performance counter registers that were only available in
    simulation.  RTL simulation now has the same number of performance counter registers available
    as on the FPGA.
  - Upgrade `tech_cells_generic` dependency to current `master`.
  - Replace custom `sram` with `tc_sram` from the `tech_cells_generic` repository.
- PULP runtime: Move memory allocators from `io` library and `libgomp` to the kernel.

### Fixed
- Hardware:
  - RI5CY/CV32E40P core:
    - Fix clearing of performance CSRs.
    - Fix stack protector (RTL simulation only) after unaligned memory access.
  - PULP cluster: Do not count accesses to the TRYX register as external memory accesses.  Even
    though such accesses target a peripheral instead of the TCDM, they have the same latency as a
    TCDM access, and they do not access any external memory.  Thus, counting them as external
    access is misleading and disturbs measurements of real external accesses.
  - Improve compatibility with Synopsys DC 2019.2 and Morty 0.5.0.
- PULP runtime: Update memory allocator from upstream to fix memory that was not freed.

### Removed
- Hardware: Remove deprecated `fpga-support` dependency.


## v0.1.3 - 2021-01-11

### Added
- Add Host library for physical memory accesses (`physmem`).

### Fixed
- Fix I/O memory accesses to PULP.  We have suffered from unreliable offloads to PULP (#87), and
  that could be caused by memory accesses from the Host to PULP that are not correctly performed to
  incorrectly configured memory mappings and/or access qualifiers.  This fixes the volatility
  correctness of `libpulp`'s `pulp_{read,write}32()` functions, which are used, among others, to
  communicate with PULP's mailbox.  This also updates the PULP Linux driver to fix potential issues
  with `mmap()`ing PULP memory regions.  Applying this fix requires recompiling
  `libomptarget.pulp.rtl.so`, `libpulp.so`, and the PULP Linux driver (`pulp.ko`); please see !214
  for instructions.


## v0.1.2 - 2020-12-15

### Added
- Root `Makefile`: Check environment also before building the PULP toolchain (`tc-pulp`), the PULP
  SDK (`sdk-pulp`), the Host SDKs (`sdk-har` and `sdk-hrv`), and the heterogeneous LLVM toolchain
  (`tc-llvm`).

### Changed
- OpenMP Examples/`helloworld`: Change to a common "Hello World!" example (instead of printing
  pointers) and clean code up.
- `petalinux/zcu102.sh` now requires the path to an existing bitstream to be defined in `local.cfg`.
  Previously, it would generate images without a bitstream, but with device tree info related to
  hardware in the PL if a `hwdef` file existed under HW.  Such images would not boot.  This change
  prevents the generation of such images.

### Fixed
- `tc-har-olinux`: Fix version of `glibc` to be compatible with libraries installed in PetaLinux
  2019.2 on ZCU102 (#95).  Applying this fix requires rebuilding the AArch64 Host toolchain and SDK;
  please see !211 for instructions.
- PULP linker script (`omptarget.ld`): Fix size of L2 (#96).  Applying this fix requires updating
  the linker script installed in the PULP SDK; please see !212 for instructions.
- OpenMP Examples/`default.mk`: Also remove `*.elf`s in `clean` recipe.


## v0.1.1 - 2020-12-03

### Added
- Add more extensive environment checks to targets in the root `Makefile`.
- PetaLinux: Add packages `util-linux{,-blkid,-lscpu}` to get essential utilities such as `taskset`.

### Fixed
- Clang/LLVM:
  - Enable compilation with debug symbols (`-g`). Prior to this fix, compilation with debug symbols
    would fail when legalizing 64-bit load/stores.
  - Fix handling of function pointers in address space assignment.  Prior to this fix, Clang could
    crash on code that used function pointers as arguments to functions.
  - Fix handling of `va_list` in address space assignment. Prior to this fix, `va_list` could not be
    used on HERO targets.
  - Machine code generation for `Xpulpv2` hardware loops:
    - Extend code generation to cases where the basic block layout changes between pre- and
      post-regalloc analyses.
    - Ensure that code generation triggers only for loops whose jump offset fits in 12 bit (which is
      the maximum encodable in the instruction).
- PetaLinux: Fix mount after boot to use `--bind` and report an error if it fails.


## v0.1.0 - 2020-11-21

First Developer Preview Release of HEROv2

### Features
- Quad-core 64-bit ARMv8 Cortex-A53 Host processor and a octa-core 32-bit RV32IMAFCXpulpv2
  accelerator, the latter as a soft-macro implemented in programmable logic, on a Xilinx Zynq
  UltraScale+ XCZU9EG MPSoC on the Xilinx ZCU102 Evaluation Board.
- Heterogeneous compiler toolchain based on LLVM 9 that enables single-source single-binary
  programming with seamless OpenMP 4.5 physically-shared-memory offloading.
  - Including compiler-generated hardware loops and load/store post-increment (features of
    `Xpulpv2`).
  - Including compiler-inferred address spaces to bridge the gap between 64-bit addresses (on the
    Host) and 32-bit addresses (on the accelerator).
- Application Programming Interface (API) for portable accelerator programming, including
  fine-grained memory allocation and asynchronous `memcpy` backed by DMA transfers.
- Heterogeneous OpenMP example applications from the linear algebra and stencil domain (ported from
  PolyBench/ACC).
- Fully open-source hardware for the accelerator, including cores, DMA engine, memory controllers,
  interconnects, synchronization hardware (e.g., mailbox), excluding only Host-side Arm and Xilinx
  IPs.
- Fully open-source software for the accelerator and the toolchain, 99% open-source software for the
  Host (the PMU firmware and the FSBL are part of Xilinx PetaLinux).
- RTL simulation environment for the accelerator, with the option to build standalone / simulation
  binaries from heterogeneous applications.
- Linux 4.19.0 (PetaLinux 2019.2) on the Host processor.
- GCC 8 `aarch64` cross compiler for standalone compilation for the Host processor (e.g., Linux,
  drivers, libraries) and GCC 7 `riscv32` cross compiler for standalone compilation for the
  accelerator (runtime libraries).
- Buildroot-based cross-root-filesystem cross compilation flow, including packages for libraries and
  drivers for the Host processor.
