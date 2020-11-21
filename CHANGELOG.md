# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).


## Unreleased

### Added

### Changed

### Fixed


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
