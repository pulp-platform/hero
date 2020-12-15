# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).


## Unreleased

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
