# HERO

The next-generation HERO, the open Heterogeneous Research Platform, combines a PULP-based open-source parallel manycore accelerator with a host running full-stack Linux. A completely open-source platform is offered with an RISC-V Ariane host processor, currently available as FPGA implementation on the Digilent Genesys 2. Moreover, a ARM version with a hard macro Cortex-A53 host can be implemented on the Xilinx ZCU102.

HERO offers a complete hardware and software platform which advances the state of the art of transparent accelerator programming using the OpenMP v4.5 Accelerator Model. The programmer can write a single application source file for the host and use OpenMP directives for parallelization and accelerator offloading. Lower-level details such as differing ISAs as well as shared virtual memory (SVM) between host and accelerator are handled by our heterogeneous toolchain based on LLVM 9, runtime libraries, kernel driver and our open-source hardware IPs.

This repository contains the top-level logic and is the entry point to the HERO infrastructure. All dependencies and the board images or simulation setups can be build from here. HERO aims to offer a complete solution with minimum prerequisites.

## Getting Started

### Prerequisites
All build steps should work on any sufficiently recent Linux version (until now only CentOS 7 is tested). Most of the core dependencies are installed automatically as part of the toolchain. Required is at least GCC 4.8 / Clang 3.3 to bootstrap the toolchain installation.

### External sources
HERO uses Git submodules that should be initialized. Either clone the repository recursively using
```
git clone --recursive <url>
```
or fetch the submodules afterwards in the repository
```
git submodule update --init --recursive
```

### Setup
All toolchains and SDKs are installed automatically to the location pointed to by the `HERO_INSTALL` environment variable. Please set it to your preferred installation location before continuing with the next step
```
export HERO_INSTALL=<your_path>
```

### Toolchains

HERO has configurations for multiple base toolchains. The project relies on Crosstool-NG for easily building the different toolchains. The toolchains are installed to the `HERO_INSTALL` directory.

All heterogeneous installations require a toolchain for the PULP accelerator, which can be built with:
```
make tc-pulp
```

Furthermore, both Linux and bare-metal toolchains are available for both the RISC-V Ariane host as for the ARMv8 Cortex-A53 host. These can be separately build as follows:
```
make tc-hrv-obare   # 64-bit RISC-V bare-metal toolchain
make tc-hrv-olinux  # 64-bit RISC-V Linux toolchain
make tc-har-obare   # 64-bit AArch64 bare-metal toolchain
make tc-har-olinux  # 64-bit AArch64 Linux toolchain
```
For all current setups only the Linux toolchains are required.

### PULP SDK
For building applications for PULP, the PULP-SDK is required. This has to be set-up before installing the HERO host SDKs as support libraries rely on it. The required configuration can be built with
```
make sdk-pulp
```

### Host SDKs
Host Software Development Kits (SDKs) for both RISC-V and ARMv8 are necessary for installing infrastructure for further build steps and are needed as well for development of heterogeneous applications as well as development on the HERO software stack itself. The SDK are generated using Buildroot and installed to the `HERO_INSTALL` directory. These SDKs can be built as follows:
```
make sdk-hrv  # SDK for RISC-V host
make sdk-har  # SDK for ARMv8 host
```

### Heterogeneous Toolchain
After the base toolchains and accelerator and host SDKs are installed, the HERO heterogeneous toolchain can be installed. The heterogeneous toolchain is based on LLVM9 and includes support in Clang and OpenMP to to create heterogeneous applications for the HERO target platform. The toolchain will be installed in the `HERO_INSTALL` toolchain folder together with the core toolchains and SDKs. To build and install the LLVM toolchain, run:
```
make tc-llvm
```

### Environments
With the toolchains and SDKs installed several development environments can be created. At the moment HERO supports two different hardware targets: (1) a fully open-source FPGA implementation with a RISC-V Ariane host and (2) an implementation with a hard-macro ARMv8 Cortex-A on the Xilinx ZCU102. Moreover, elementary simulation targets are available for (1) the RISC-V host infrastructure using QEMU and (2) the PULP accelerator for RTL verification in Modelsim.

##### Digilent Genesys 2
*NOTE: A complete FPGA bitstream for this platform is currently not available for external distribution yet*

A complete Linux environment with kernel and the base root filesystem for the Digilent Genesys 2 environment can be built with:
```
make br-har-ediggenesys2
```
This will eventually create a binary `hrv-ediggenesys-base-bbl.bin` in the `output` folder. This binary should be put on a SD-card for it to be loaded on the board. On the SD-card a GPT partition table is required to be created first (this step is needed only once). Be *CAREFUL* to execute the following steps on the correct partition and device (the SD-card).
```
# fdisk -l # search for the disk label of the SD-card (e.g. /dev/sdx)
# sgdisk --clear --new=1:2048:67583 --new=2 --typecode=1:3000 --typecode=2:8300 /dev/sdx # create a new gpt partition table and two partitions: 1st partition: 32mb (ONIE boot), second partition: rest (Linux root)
```
The system binary can the be copied onto the SD-card using the disk partition created before, be *CAREFUL* again not to overwrite the wrong device:
```
# dd if=output/hrv-ediggenesys-base-bbl.bin of=/dev/sdx1 status=progress oflag=sync bs=1M
```
If the FPGA bitstream is programmed correctly and the SD-card is put in, the system can then be booted up! To develop applications for this setup the dynamic environment can be loaded using `source env/ediggenesys2.sh`. Afterwards applications can be built and transferred directly to the board.

Currently the default MAC address is not loaded from the device, but fixed in the bitstream instead. It should be changed to allow for different devices on the same network. To achieve this the system configuration can be customized by adding a single line with value `BR2_PACKAGE_ARIANE_SUPPORT_ETH_MAC="<custom-mac>"` to a file `local.cfg` in the root repository (create it if it does not yet exist). After changing this configuration parameter, the Ariane support package needs to be rebuild, this can be achieved with `make -C output/br-har-ediggenesys2 ariane-support-dirclean` and then rerunning `make br-har-ediggenesys2` from the top-level directory of the repository.

As on Ariane loading images from the SD card is currently limited and the root filesystem is not preserved on reboots, the base image does not directly contain the entire HERO infrastructure. A development filesystem based on the corresponding host SDK can be mounted externally instead. It is recommended to mount these images via NFS, the target filesystem can be extracted from `output/hrv-rootfs.tar`. This filesystem can be mounted automatically on boot by adding a configuration line with value `BR2_HERO_EXT_MOUNT="<mount-options> <ip>:<path>"` in `local.cfg` and then updating the image by rerunning `make br-har-ediggenesys2`.

##### Xilinx ZCU102
*NOTE: A functional FPGA bitstream for this platform is currently not available for external distribution yet*

A complete Linux environment with kernel and the base root filesystem for the ARMv8 host on the Xilinx Zynq Ultrascale+ MPSoC ZCU102 can be built with:
```
make br-har-exilzcu102
```
This generates a SD-card image containing the complete infrastructure and fully ready to be booted directly. It can be loaded on a SD-card as follows, but *CAREFUL* action is required to not overwrite the wrong device.
```
# fdisk -l # search for the disk label of the SD-card (e.g. /dev/sdx)
# dd if=output/har-exilzcu102-base-bbl.bin of=/dev/sdx status=progress oflag=sync bs=1M # write the image on the SD-card
```
Afterwards the system can be booted up after configuring the ZCU102 board jumpers to boot from the SD-card. To develop applications for this setup the dynamic environment can be loaded using `source env/exilzcu102.sh`. Afterwards applications can be built and transferred directly to the board.

The host processor is implemented is provided as a hard-macro, allowing the FPGA implementation of the accelerator to be loaded later during boot. An bitstream with the hardware implementation can be loaded automatically by adding `BR_HERO_BITSTREAM=<path_bitstream>` in `local.cfg` and rebuilding the image with `make br-har-exilzcu102`.

Similary to the RISC-V setup, the base image does currently not contain the entire HERO infrastructure. A development filesystem based on the corresponding host SDK can be mounted externally instead, for example via NFS. The target filesystem can be extracted from `output/hrv-rootfs.tar`. This filesystem can be mounted automatically on boot by adding a configuration line with value `BR2_HERO_EXT_MOUNT="<mount-options> <ip>:<path>"` in `local.cfg` and then updating the image by rerunning `make br-har-exilzcu102`.

##### QEMU RISC-V
For host debugging it can be useful to test the environment first with the QEMU machine emulator. A clone of the RISC-V Ariane environment without specific hardware patches and including virtual drivers instead, can be built with:
```
make br-hrv-eqemu
```
A recent version of QEMU is required to be able to emulate RISC-V, it is currently recommended to build it from [source](https://github.com/qemu/qemu). After installation the following configuration can be used to bootup
```
qemu-system-riscv64 \
   -machine virt -nographic \
   -kernel output/hrv-eqemu-base-bbl.bin \
   -append "root=/dev/vda ro" \
   -drive file=output/hrv-eqemu-base-rootfs.ext2,format=raw,id=hd0 \
   -device virtio-blk-device,drive=hd0 \
   -netdev user,id=net0,hostfwd=tcp::5555-:22 \
   -device virtio-net-device,netdev=net0 \
   -device virtio-rng-device \
   -gdb tcp::3332

```
It it possible to SSH to the machine on port 5555 and debug with GDB on port 3332.

A root filesystem with the entire HERO infrastructure can be loaded in QEMU by adding
```
   -drive file=output/hrv-rootfs.ext4,format=raw,id=hd1 \
   -device virtio-blk-device,drive=hd1 \
```
to the command to run above. Afterwards `chroot /mnt` can be executed to change to the HERO environment.

##### PULP RTL Simulation
An environment is provided to simulate the PULP accelerator in RTL. When the Modelsim package is available the simulation infrastructure can be initialized as follows:
```
cd hardware
make
cd vsim
./compile.sh
```

For building applications for the simulation, the dynamic environment can be loaded with `source env/esim.sh`. When building OpenMP applications it has to be specified to build them only for PULP using `make only=pulp`. The application name `<app_name>` is the path to the directory from the `openmp-examples` directory (for example `polybench-acc/2mm`). Afterwards the binary can be loaded in the simulator with:
```
cd hardware/test
./gen_slm_files.sh <app_name>
cd ../vsim
./start_sim.sh
```

### Tools
For development with RISC-V hardware the OpenOCD debugger can become useful. To simplify installation a target is provided that installs the debugger automatically to the `HERO_INSTALL` toolchain installation directory using
```
make tools-hrv-openocd
```
