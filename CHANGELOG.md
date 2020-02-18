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

### Changed
- Replace `axi_node` with standard-compliant crossbar `axi_xbar`.
- Move `soc_peripherals` from testbench to `soc_bus`. Most importantly, this includes the `soc_control_registers`.

### Fixed
- `axi2mem`: Ensure starvation freedom when prioritizing individual writes over read bursts.
- `riscv`: Propagate enabled A extension to MISA CSR.
