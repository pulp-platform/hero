# OpenMP Offloading Stack Summary

This document briefly describes the interaction between the SW stack components
that are involved in the OpenMP offloading operation.

# Main host-side libraries

There are three main layers of the software stack that perform the offloading,
described briefly below.

## PULP OpenMP Offloading Plugin for LLVM

Location: `toolchain/llvm-project/openmp/libomptarget/plugins/pulp/rtl.cpp`

This file implements the top-level logic for the offloading, in particular the
functions that are named `__tgt_rtl_*`. Calls to the target agnostic
`libomptarget` interface (`hero/toolchain/llvm-project/openmp/libomptarget`, see
further
[this presentation](https://llvm-hpc3-workshop.github.io/slides/Bertolli.pdf)
starting on Slide 15) are inserted by Clang on the expansion of OpenMP pragmas.
This target-agnostic library in turn invokes the PULP OpenMP Offloading Plugin.

It implements high level functionality like device side buffer allocation
(`alloc`), host-to-device (`submit`) and device-to host (`retrieve`) data
transfers, as well as the top-level routine to start the offloading.

## GNU OpenMP compatibility layer

Location:
`toolchain/llvm-project/openmp/libomptarget/plugins/pulp/plugin-pulp-hero.h`

The core glue code for performing the operations discussed in the previous
section are implemented in the GNU OpenMP library, which is implemented in this
file. It is based on the GNU OpenMP implementation performing similar operations
that was used for the previous versions of HERO.

Functions implemented here are prefixed `GOMP_OFFLOADING_*`.

## PULP Library

Location: `support/libpulp`

This library implements the low level functionalities to interact with PULP
through the various kernel routines and memory mapped communication methods.

It implements functions that are prefixed `pulp_`, and deal with things such as
L3 allocation (`l3_alloc`), and communication via the mailbox (`mbox_read`,
`mbox_write`).

# Offloading Operation

NOTE: The printouts referenced in this section depend on the debug level
configured in the previously mentioned libraries.

Operationally, the key interactions between host and PULP are managed from the
offloading plugin `rtl.cpp` (calling into lower levels of the stack). 

Overall the interaction is: *Your compiled code* interacts with `rtl.cpp` (`__tgt_rtl_*` functions) interacts with `plugin-pulp-hero.h` (`GOMP_OFFLOAD_*` functions) which in turn interact with `hero/support/libpulp` (`pulp_*` functions).

What happens is typically:

* Load all parts of the RISCV ELF binary into PULP memory (L2 typically, but also L1), e.g.,
   ```
   Target PULP RTL --> writing ELF segment [0x00000000100000b4, 0x0000000010000a60]
   Target PULP RTL --> to device L1
   Target PULP RTL --> *** wrote 416 bytes, zeroed 2060 bytes
   ```

* Handle the L3 allocation (`_alloc`) and transfer (`to`/`tofrom`: `_submit`, and `tofrom`/`from`: `_retrieve`) of PULP-buffers for OpenMP `map()`ed data structures, e.g.,
   ```
   Target PULP RTL --> __tgt_rtl_data_alloc(device_id=1, size=346112, hst_ptr=0x0000000024e6f5e0)
   Target PULP RTL --> __tgt_rtl_data_submit(device_id=1, tgt_ptr=0x000000008007f880, hst_ptr=0x0000000024e6f5e0, size=346112
   ```

* Use mailbox (via `pulp_mbox_*` functions) to exchange commands to PULP, such as:
   - the address of the kernel to run, printed during execution as
      ```
      Target PULP RTL --> found __omp_offloading_803_36de11ab_gemm_nn_l155 at 0x000000001c00062c
      ```
   - the list of arguments, printed during execution as
      ```
      Target PULP RTL --> Offload Args (0x32811c20): 0x0000000080000080, 0x000000008007f880, 0x00000000800d4080, 0x00000000800fe060, 0x00000000000000ff, 0x0000000000000200, 0x0000000000000200, 0x00000000000000a9, 0x00000000000000a9, 0x00000000000000a9,
      ```
   - and starting the computation by sending the start command.

# Device-side libraries

The LLVM-specific PULP-side OpenMP library is located at
`pulp/sdk/runtime/libomptarget-pulp-rtl`. It implements things such as
`parallel` and `for schedule(static)` etc. on PULP, in accordance with the KMP
interface used by LLVM.

There are also several other libraries that perform lower-level tasks (such as
the offload manager) that should be better documented here. Overall, most
PULP-side libraries can be found in `pulp/sdk/runtime`.
