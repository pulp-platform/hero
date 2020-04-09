# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## Unreleased
### Added

### Changed
- Decrease L2 size to 128 KiB.
- `pulp_cluster`:
  - Decrease TCDM size to 128 KiB.

### Fixed

### Removed
- PULP runtime: Remove broken `rt_*_alloc_align` functions.  These functions did not correctly
  return aligned memory.  The allocator in the PULP runtime is not suitable for aligned allocations.
  If aligned allocations are required, a different allocator needs to be implemented (e.g.,
  page-based).  It's quite common for RTOSes (e.g., Zephyr) to not support aligned allocation.


## 2020-03-14
### Changed
- Move the `soc_peripherals` out of PULP into the testbench.
- Disable atomic operations at L2 memory, filter ATOPs at cluster output.
- Make all AXI transactions issued by the cores non-modifiable.

### Fixed
- `event_unit_flex`: Fix update condition for `r_valid` which fixes the multi-cycle `r_valid` in
  RI5CY's LSU.
- Synthesis:
  - Fix multicycle path constraints of instruction cache.
  - Add missing elaboration/analysis commands for `axi_burst_splitter`, `axi_mem_if`, `axi_tcdm_if`,
    `core2axi`, `debug_system`, and `riscv-dbg`.
- Improve compatibility with VCS 2017.03 by avoiding the following unsupported SystemVerilog
  constructs: `assert property`, `assume property`, `package automatic`, and `unique0 case`.
  Furthermore, exclude any test code that is not required for the top-level testbench.
- Improve compatibility with DC 2018.06 by replacing the call to `$clog2` in `soc_bus_pkg` by an
  equivalent constant function implementation (`cfg_math_pkg::clog2`).
- `rr_arb_tree`: Fix width of ports for `NumIn == 1`.
- `axi_xbar`: Fix width of ports and signals for `NoMstPorts == 1`.
- `pulp_tb`: Add missing `mailbox_evt_i` connection for `pulp`.
- `fifo_v3`: Predefine constant for last valid pointer index to enforce correct behavior in VCS
  2017.03.


## 2020-03-06
### Added
- Add Virtual Platform for PULP at `pulp/virtual-platform`.

### Changed
- `example-apps`: Remove the heterogeneous OpenMP functions not supported by GCC from the `helloworld` app.
- Align memory sizes in `pulp/sdk` to 320KiB of L1 memory and 256KiB of L2 memory
- `pulp/sdk`: Update DMA library version to `mchan_v7`.
- `pulp_tb`: Remove unused ports on `axi_xbar`

### Fixed
- `setup.sh`: Build PULP SDK in setup script.
- `pulp/sdk`:
  - Include all the SDK's submodules in the package.
  - Match memory sizes and addresses of cluster components with the hardware.
- `axi_dwc`: Fix incorrect handling of bursts in upsizer.
- `axi_top_filter`:
  - The master interface of this module in one case depended on `aw_ready` before applying
    `w_valid`, which is a violation of the AXI specification that can lead to deadlocks.  This issue
    has been fixed by removing that dependency.
  - The slave interface of this module could illegally change the value of B and R beats between
    valid and handshake.  This has been fixed.


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
