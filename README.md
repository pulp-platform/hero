# HERO

The next-generation HERO, the open Heterogeneous Research Platform, combines a PULP-based open-source parallel manycore accelerator with a host running full-stack Linux.  This version targets the Xilinx ZCU102 board, combining a hard-macro Cortex-A53 host CPU with a PULP accelerator on the programmable logic (PL).

HERO offers a complete hardware and software platform which advances the state of the art of transparent accelerator programming using the OpenMP v4.5 Accelerator Model. The programmer can write a single application source file for the host and use OpenMP directives for parallelization and accelerator offloading. Lower-level details such as differing ISAs as well as shared virtual memory (SVM) between host and accelerator are handled by our heterogeneous toolchain based on LLVM 9, runtime libraries, kernel driver, and our open-source hardware IPs.

This repository contains the top-level logic and is the entry point to the HERO infrastructure. All dependencies and the board images or simulation setups can be built from here. HERO aims to offer a complete solution with minimum prerequisites.

## Getting Started

### Prerequisites
All build steps should work on any sufficiently recent Linux distribution (we have automated tests on CentOS 7). Most of the core dependencies are installed automatically as part of the toolchain. Required is at least GCC 4.8 / Clang 3.3 to bootstrap the toolchain installation.
More details can be found [here](PREREQUISITES.md).

### External sources
HERO uses Git submodules that have to be initialized.  When you have already cloned the repository, use
```
git submodule update --init --recursive
```
to fetch the submodules.

### Setup
All toolchains and SDKs are installed automatically to the location pointed to by the `HERO_INSTALL` environment variable. Please set it to your preferred installation location before continuing with the next step
```
export HERO_INSTALL=<your_path>
```
We recommend you create an `install` subdirectory in this repository and set `HERO_INSTALL` to that.

### Toolchains

HERO has configurations for multiple base toolchains. The project relies on Crosstool-NG for easily building the different toolchains. The toolchains are installed to the `HERO_INSTALL` directory.

All heterogeneous installations require a toolchain for the PULP accelerator, which can be built with:
```
make tc-pulp
```

Furthermore, both Linux and bare-metal toolchains are available for the ARMv8 Cortex-A53 host. These can be separately build as follows:
```
make tc-har-obare   # 64-bit AArch64 bare-metal toolchain
make tc-har-olinux  # 64-bit AArch64 Linux toolchain
```
Current setups require only the Linux toolchain (`-olinux` suffix).

### PULP SDK
The PULP SDK is required to build applications for PULP. This has to be set up before installing the HERO host SDKs because support libraries rely on it. The required configuration can be built with
```
make sdk-pulp
```

### Host SDKs
Host Software Development Kits (SDK) for ARMv8 is necessary for the infrastructure of further build steps, for the development of heterogeneous applications, and for development on the HERO software stack itself. The SDK is generated using Buildroot and installed to the `HERO_INSTALL` directory. The SDK can be built as follows:
```
make sdk-har  # SDK for ARMv8 host
```

### Heterogeneous Toolchain
After the base toolchains and accelerator and host SDK are installed, the HERO heterogeneous toolchain can be installed. The heterogeneous toolchain is based on LLVM9 and includes support in Clang and OpenMP to create heterogeneous applications for the HERO target platform. The toolchain will be installed in the `HERO_INSTALL` toolchain folder together with the core toolchains and SDKs. To build and install the LLVM toolchain, run:
```
make tc-llvm
```

### Environments
With the toolchains and SDKs installed, several development environments can be created. At the moment, HERO supports an implementation with a hard-macro ARMv8 Cortex-A on the Xilinx ZCU102. Moreover, an elementary simulation target is available for the PULP accelerator in an RTL simulator (QuestaSim).

##### Xilinx ZCU102
First, generate the bitstream and Vivado HDF files:
```
cd hardware/fpga
make
```
Next, build the images for a complete Linux environment with kernel and the base root filesystem for the ARMv8 host on the Xilinx Zynq UltraScale+ MPSoC ZCU102 with:
```
make br-har-exilzcu102
```
This generates a SD card image containing the complete infrastructure and fully ready to be booted directly. It can be loaded on a SD card as follows, but *CAREFUL* action is required to not overwrite the wrong device.
```
# fdisk -l # search for the disk label of the SD-card (e.g. /dev/sdx)
# dd if=output/har-exilzcu102-base-bbl.bin of=/dev/sdx status=progress oflag=sync bs=1M # write the image on the SD-card
```
Afterwards the system can be booted up after configuring the ZCU102 board jumpers to boot from the SD card. To develop applications for this setup, the dynamic environment can be loaded using `source env/exilzcu102.sh`. Afterwards applications can be built and transferred directly to the board.

The host processor is implemented as a hard-macro, allowing the FPGA implementation of the accelerator to be loaded later during boot. A bitstream with the hardware implementation can be loaded automatically by adding `BR_HERO_BITSTREAM=<path_bitstream>` in `local.cfg` and rebuilding the image with `make br-har-exilzcu102`.

Similarly to the RISC-V setup, the base image does currently not contain the entire HERO infrastructure. A development filesystem based on the corresponding host SDK can be mounted externally instead, for example via NFS. The target filesystem can be extracted from `output/hrv-rootfs.tar`. This filesystem can be mounted automatically on boot by adding a configuration line with value `BR2_HERO_EXT_MOUNT="<mount-options> <ip>:<path>"` in `local.cfg` and then updating the image by rerunning `make br-har-exilzcu102`.

##### PULP RTL Simulation
An environment is provided to simulate the PULP accelerator in RTL. If QuestaSim is installed, the simulation infrastructure can be initialized as follows:
```
cd hardware
make
cd vsim
./compile.sh
```

For building applications for the simulation, the dynamic environment can be loaded with `source env/esim-exilzcu102.sh`. When building OpenMP applications, it has to be specified to build them only for PULP using `make only=pulp`, which will also generate SLM files to initialize memory in simulation. Afterwards, the binary can be loaded in the simulator with:
```
cd hardware/vsim
../test/gen_slm_files.sh <app_name>
./start_sim.sh
```
where `<app_name>` is the path to the directory from the `openmp-examples` directory (for example `polybench-acc/2mm`).
