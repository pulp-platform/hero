# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]
### Added
- Add debug module `riscv-dbg` v0.3
- Add `axi_mem_if` fix-name-conflict
- Add `debug_subsystem` for RISC-V compliant external debug support (spec v0.13)
- Add `dm_test`, a debug module testbench
- Initial development
- Readd `pulp-sdk`

### Changed
- Replace `axi_node` with standard-compliant crossbar `axi_xbar`.
- Move `soc_peripherals` from testbench to `soc_bus`. Most importantly, this includes the `soc_control_registers`.
- Change the AXI burst type of the cluster from `FIXED` to `INCR`.
- Replace deprecated `axi2apb` module with `axi_to_axi_lite` and `axi_lite_to_apb` module.
- Match boot address with Hero (`0x1C00_8080` --> `1C00_0080`)
- Match `soc_peripherals` address with Hero
- Change boot behavior of `pulp-runtime` to match Hero's
- Rename env script for minimal runtime to `ehuawei-minimal-runtime.sh`

### Fixed
- `axi2mem`: Ensure starvation freedom when prioritizing individual writes over read bursts.
- `riscv`: Propagate enabled A extension to MISA CSR.
- `axi_dwc`: Ensure the W beat is sent even if the AW is not yet accepted.
- Remove FLL configuration in `pulp-runtime`.
