# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## Unreleased
### Added

### Changed

### Fixed
- `setup.sh`: Build PULP SDK in setup script.


## 2020-02-28
### Added
- Add debug module `riscv-dbg` v0.3.
- Add `axi_mem_if` as dependency of `riscv-dbg`.
- Add `debug_subsystem` for RISC-V-compliant external debug support (spec v0.13).
- Add `dm_test`, a debug module testbench.
- Re-add `pulp-sdk`.
- Add syn, pnr, and topographical syn scripts.
- Add event line for mailbox.
- Add tests for DMA (`mchan`).

### Changed
- Replace `axi_node` with standard-compliant crossbar `axi_xbar`.
- Move `soc_peripherals` from testbench to `soc_bus`. Most importantly, this includes the `soc_control_registers`.
- Replace deprecated `axi2apb` module with `axi_to_axi_lite` and `axi_lite_to_apb` module.
- Match boot address with HERO (`0x1C00_8080` --> `1C00_0080`).
- Match `soc_peripherals` address with HERO.
- Change boot behavior of `pulp-runtime` to match HERO's.
- Rename env script for minimal runtime to `ehuawei-minimal-runtime.sh`.
- Re-enable atomics at L2.
- `pulp_cluster`:
  - Change the AXI burst type from `FIXED` to `INCR`.
  - Insert spill (pipeline) registers on request paths into `axi2mem` to break long paths.
  - Change burst length of `mchan` from 256 to 128.
  - Increase TCDM size to 320 KiB.
  - `hier-icache`: Remove prefetch feature and add pipelines on both request and response paths to improve timing.
- Change AXI ID width to 6 (cluster slave side) and to 8 (SoC slave side).
- `sram`: Modify memory cut size for the extended TCDM.

### Fixed
- `axi2mem`: Ensure starvation freedom when prioritizing individual writes over read bursts.
- `riscv`: Propagate enabled A extension to MISA CSR.
- `axi_dwc`: Ensure the W beat is sent even if the AW is not yet accepted.
- Remove FLL configuration in `pulp-runtime`.
- `axi_riscv_atomics`: Improve compatibility with VCS.
- `pulp_cluster`: The AxCACHE signal is no longer statically set to *Normal Non-Cacheable
  Non-Bufferable* but properly fed through from internal masters.  Accesses by the instruction cache
  and the DMA unit are now *Modifiable* for efficient reshaping downstream.
- In the linker script of `pulp-runtime`, `__l2_shared_end` was computed wrong.  This has been
  corrected to the last address of the `L2` memory section.
- `riscv`: Fix FPU parameters to correctly pipeline the FPUs.
- `hier-icache`: Fix instruction cache bypass.
