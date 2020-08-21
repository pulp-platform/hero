# Changelog
All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/).


## Unreleased
### Added

### Changed

### Fixed


## 2020-08-21
### Fixed
- Enable hard-floats in Newlib standard library and PULP SDK libraries.


## 2020-07-26
### Fixed
- `fpnew_pkg`: Rewrite `bias` function to improve compatibility with FPGA synthesis tool.
- `register_file_2r_2w_icache`: Fix cache line writing on FPGA.


## 2020-07-14
### Fixed
- `axi_dw_downsizer` and `debug_system`: Cut W channel to break combinational loop.


## 2020-07-10
### Added
- Add OpenOCD scripts for debugging with GDB; see `hardware/README_DEBUG.md` for details.


## 2020-07-09-1
### Fixed
- `axi_pkg`: Reapply patch "Remove `enum`ness of `xbar_latency_e` to improve compatibility with some
  formal tools".


## 2020-07-09
### Added
- `debug_system`: Add OpenOCD tests.

### Changed
- `axi_dwc`: Update to upstream v0.22.0.  The downsizer now lets AXI transactions narrower than the
  downstream data width pass through unmodified, and it downsizes transactions also without the
  Modifiable bit set.

### Fixed
- `axi_dwc`: Fix overflow of B forward FIFO in downsizer.  The downsizer is used for memory accesses
  to the debug system.


## 2020-06-30
### Changed
- `pulp_cluster`:
  - Increase depth of buffers in DMA `trans_unit` to 4 and add a register on the W channel of the
    cluster crossbar to reduce the number of idle bus cycles between DMA bursts.
  - Increase maximum number of in-flight DMA transactions to 32.
- `fpnew`, `riscv-dbg`, `tcdm_interconnect`: Change syntax of some type casts to improve
  compatibility with some tools.

### Fixed
- `axi_to_mem` and `core_demux`: Remove `'x` default assignments.
- `register_file_2r_2w_icache`: Fix enable condition in FF mode.
- `riscv` core: Provide legal value in Debug Trigger Info CSR.


## 2020-06-23
### Added
- `hier-icache`: Add implementation alternatives of data and tag memories of the instruction cache.
  The following options can be selected via `define`s:
  - Defining `RF_1R1W_FF` and `RF_2R2W_FF` means that the 1R/1W and 2R/2W register files are
    implemented with flip-flops (FFs) instead of latches.
  - Defining `ICACHE_L1_DATA_SRAM` means that the L1 data memory is implemented with two-port (one
    read and one write port) SRAM.

### Changed
- `pulp`: Tie `ref_clk_i` of cluster off to prevent timing conflicts.

### Fixed
- `fpnew`:
  - Fix undriven unused signals in multi-fmt blocks.
  - Fix undriven portions of result in multi slices.


## 2020-06-16
### Added
- PULP SDK/`librtio`: Add support for floats in `printf`.
- `pulp` top-level HW module: Add `jtag_tdo_en_o` output pin connected to JTAG debug module.

### Changed
- Prefix types in `axi2mem`, `axi_xbar`, and `axi_cut_intf` to prevent type collisions in some
  tools.
- `axi_pkg`: Remove `enum`ness of `xbar_latency_e` to improve compatibility with some formal tools.

### Fixed
- `axi_id_remap` and `id_queue`: Remove `'x` default assignments.
- `cluster_interconnect_wrap`: Tie unused input of `i_arb` off.
- `event_unit_flex`: Add parentheses around OR-reduction.
- `fpnew_pkg`: Fix definition of `opgrp_fmt_unit_types_t`.
- `hier-icache`:
  - Fix width mismatch and default branch issue.
  - Fix non-blocking assignment.
- `riscv_core`: Fix declaration of `mult_is_cplx_ex`.
- PULP SDK/`librtio`: Fix pointer arithmetic in `l1malloc`, `l1free`, `l2malloc`, and `l2free`.


## 2020-05-20
### Added
- `sram`: Add DFT ports.

### Changed
- `axi` and `common_cells`: Export include directory `include/axi` and `include/common_cells`,
  respectively, to improve compatibility with tools that do not support directories in SystemVerilog
  `` `include``.
- `axi2mem`: Improve tool compatibility by separating modules into individual files.
- `fpnew`:
  - Add `default` to `unique case` that does not need a default to improve tool compatibility.
  - Flatten `opgrp_fmt_unit_types_t` to improve tool compatibility.
- `pulp_cluster`:
  - Reduce address range of event unit in `core_demux`.
  - Swap peripheral IDs of error slave (now 7) and external port (now 8).
  - Prefix AXI channel and request/response types to prevent type collisions in some tools.
- Rename `fifo` to `pulp_fifo` to prevent naming collisions with external modules.
- Replace `localparam` in parameters of all modules by `parameter` to improve tool compatibility.
- Rename `SYNTHESIS` define to `TARGET_SYNTHESIS` to prevent collisions in some synthesizers.

### Fixed
- `common_cells`: Add missing synthesis guard around assertion in `rstgen_bypass`.
- `fpu_div_sqrt_mvp` and `fpu_interco`: Improve tool compatibility by removing wildcard imports.
- `hier-icache`:
  - Remove unused BIST ports.
  - Fix deadlock on write to `0x18` register (prefetch enable).
  - Fix upper bound of `for` loop
- `pulp_cluster`:
  - Disconnect external bus from cluster peripherals.
  - Tie unused `s_hwpe_cfg_bus.r_opc` off.
  - Tie unused `debug_bus` signals off.
- `pulp_cluster_ooc`: Tie unused ports off.
- `pulp-runtime`: Enable RISC-V A extension in compilation flow.
- `riscv`:
  - Remove unused BIST ports from register file.
  - Remove wildcard imports to improve tool compatibility.
- `scm`:
  - Remove unused BIST ports.
  - Fix blocking to non-blocking assignment in `register_file_1r_1w`.
- `soc_bus`:
  - Fix number of slave ports.
  - Fix contiguous assignment to `cluster_base_addr` and `l2_port_base_addr`.


## 2020-05-06
### Added
- Add Spyglass configuration.

### Changed
- `pulp_cluster`
  - `core_region`: Remove `periph_demux`, which is no longer used.
  - Remove `s_core_dmactrl_bus`, which is no longer used.
  - Register `dbg_irq_valid` before synchronizer.
  - `cluster_bus_wrap`: Replace `axi_xbar` with `axi_xbar_intf` to improve tool compatibility.
- `axi_xbar` and `axi_lite_xbar`: Replace `Cfg` struct parameter by flat list of parameters.

### Fixed
- `fpnew_pkg`: Remove enums from `typedef` source type to improve compatibility with Cadence VXE.
- `fpnew_cast_multi`: Replace assignment to `QNAN_EXPONENT` to improve compatibility with Cadence
  VXE.
- `gf22fdx/synopsys`: Fix synthesis constraints of instruction cache.
- `hier-icache`:
  - Fix connection of `perf_cnt_L1[0..7`].
  - Fix writing of `sel_flush` register.
  - Add missing DFT inputs to `ram_ws_rs_data_scm`.
  - Connect `test_en_i` to `register_file_1r_1w_test_wrap` in `ram_ws_rs_data_scm` and
    `ram_ws_rs_tag_scm`.
- `pulp_cluster`:
  - Tie `core_halted_i` input off and remove `dbg_core_halted`, which is no longer used.
  - `periph_interconnect`: Fix addressing loop in `0x1020_1C00..0x1020_1FFF` memory range.
  - Remove duplicate definition of `axi_slice_wrap` module.
- `axi_slice_dc`: Remove duplicate definition of `axi_cdc` module.
- Remove wildcard imports in `pulp` and `pulp_cluster_ooc` to improve compatibility with tools that
  cannot correctly resolve import symbol conflicts.


## 2020-04-24
### Added
- Add DFT input signals `mem_ctrl`, `dft_ram_gt_se`, `dft_ram_bypass`, `dft_ram_bp_clk_en` to
  top-level `pulp` module and propagate the inputs to all modules instantiating `sram`s.
- Add DFT input signal `dft_mode` to top-level `pulp` module and connect it to the debug system
  (`i_debug_system`).
- Add DFT input signal `dft_glb_gt_se` to top-level `pulp` module and connect it to the test mode or
  test enable pin of clock gates.

### Changed
- `soc_bus`: Map `0x0000_0000..0x0FFF_FFFF` address region to external port (to host).
- If `dft_mode` is set, reset can only be triggered by the `rst_ni` input and not by the `dm_top`
  debug module.

### Fixed
- Virtual Platform: Fix changed address of SoC peripherals in Boot ROM.
- `pulp_cluster`:
  - Fix signal assignments when there is no `priv_icache`.
  - Fix event unit port on peripheral interconnect.  The previous port combination led to responses
    on two ports of the peripheral interconnect upon an access to one of the ports.  This has been
    changed so that all event unit addresses on the peripheral interconnect are decoded to the first
    port and the second port is tied off.
  - Decode accesses to non-present HWPE to the error slave so they properly return errors instead of
    never handling requests.
  - `per2axi`: Fix handshake on `per_slave` port that could cause transactions to be lost.
- `riscv`: Fix clearing of performance counter (PC) control and status registers (CSRs).
- `axi_to_mem`: Improve compatibility with Cadence VXE.

### Removed
- `pulp_cluster`: `rstgen` has been removed from the synchronous cluster.


## 2020-04-15
### Added
- Add support for custom `hua20` RISC-V machine architecture extension in GCC.  This comprises all
  the custom instructions of the `gap9` extension plus pipeline scheduling for two cycles FPU
  latency.
- `SimJTAG`: JTAG DPI bridge for simulation that can be enabled with `+define+USE_JTAG_DPI`.
- `remote_bitbang`: DPI library that allows communication between OpenOCD and the JTAG DPI bridge.
- `debug_system`: non-debug-module reset (`ndmreset`) capabilities, which allows the debug module to
  control the system reset.

### Changed
- Update instruction cache (`hier-icache`) to improve timing.
- Change L2 memory controller to multiple ports (banking factor of 2) to achieve full duplex
  throughput of L2 AXI port.
- `pulp`:
  - As the cluster never issues atomic operations (ATOPs) at its AXI master port (see below),
    remove the ATOP filter between cluster and SoC bus.
  - Move port types from parameters into package.
  - Change ID width of external slave port to 8 bit.
  - Change address of external peripherals to `0x1D10_0000`.
- `pulp_cluster`:
  - Disable ATOPs in `per2axi` and redirect transactions that would be ATOPs to error slave in SoC
    bus (at address `0x1B00_....`).
  - Reduce maximum size of a DMA burst to 128 B.
  - Reduce maximum number of in-flight DMA transactions to 16.
- `soc_bus`: Assign a single, contiguous address region to external port (to host), map all holes in
  the address map of this bus to the error slave.

### Fixed
- `pulp_tb`: Tie unused `ext_evt_*_i` off.
- `pulp_cluster`:
  - `amo_shim`: Fix synthesis warnings (out of bounds) related to 64-bit support.
  - `cluster_bus_wrap`: Fix TCDM address space to the full size of the TCDM.
  - `cluster_interconnect_wrap`:
    - Add missing `default` in `unique case` statement.
    - Remove gaps and aliases in address map of peripherals.  Requests to any address not matching a
      peripheral are now responded with errors.
- `soc_bus`: Fix cluster address space to include the entire peripheral space.
- Synthesis elaboration scripts: Add missing `axi_serializer`.


## 2020-04-13
### Fixed
- `riscv` core:
  - Remove `stall_full` signal, which was causing a combinatorial loop and was never triggered with
    new `apu_dispatcher` changes.
  - Adjust `csr_apu_stall` signal in the `id_stage` according to the new floating-point latencies.


## 2020-04-10
### Added
- Add three event lanes for external events, mapped to the cluster event map.
- Add GDB to the PULP toolchain.

### Changed
- Decrease L2 size to 128 KiB and increase depth of each bank to 2048 rows.
- `pulp_cluster`:
  - Decrease TCDM size to 128 KiB.
  - Modify APU Dispatcher, Decoder, and FPU Demux to allow back-to-back issuing of up to 3 cycle FPU
    instructions without stalling:
    - Modify the FSM inside the FPU Demux such that it will not stop new requests to wait for the
      previous to complete.
    - Change how the latency is encoded for FPU instructions inside the decoder.  `latency = 0` now
      encodes instructions that takes more than 3 cycles to complete.
    - Modify the APU Dispatcher to allow up to 3 cycle latency FPU instructions to be issued
      back-to-back.  Instructions with `latency = 0` (division and other instructions that take more
      than 3 cycles) now always stall the pipeline.
  - Add second pipeline stage to FPU.
  - Remap all DMA and instruction cache AXI transactions to a single ID.  This is necessary as the
    DMA engine and the instruction cache do not support interleaved responses, and it helps reducing
    the AXI ID width of the system.
  - Decrease AXI input ID width to 3 bit and output ID width to 5 bit.  This reduces the
    complexity of the AXI interconnects.
  - Cut all AXI channels through `axi2mem` to break long paths between TCDM interconnect and
    instruction cache.
- Update `common_cells` to v1.16.4 to fix generation of `head_tail_q` registers.
- Update AXI modules to v0.18.1 to fix problems with DWC.
- Reduce data width of SoC bus to 64 bit and remove data width converters and buffers, which are now
  unnecessary.

### Fixed
- Add `is_decoding` signal to mask `read_dependency` inside `APU_Dispatcher`. This fixed a bug that
  incorrectly detected a read dependency when a `fetch_fail` occurred.
- `pulp_cluster`: Remove unused `dc_token_ring_fifo_dout` to prevent triggering `soc_periph_evt`.
- `axi2mem`: Fix bug that could lead to corruption of AMO execution.
- `amo_shim`: Fix adherence to and forwarding of byte strobe.
- `riscv`: Disable inference of FP registers and latches when `Zfinx` is enabled.

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
- `axi_atop_filter`:
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
