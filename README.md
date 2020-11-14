# HERO

The next-generation HERO, the open Heterogeneous Research Platform, combines a PULP-based open-source parallel manycore accelerator with a host running full-stack Linux. A completely open-source platform is offered with an RISC-V Ariane host processor, currently available as FPGA implementation on the Digilent Genesys 2. Moreover, a ARM version with a hard macro Cortex-A53 host can be implemented on the Xilinx ZCU102.

HERO offers a complete hardware and software platform which advances the state of the art of transparent accelerator programming using the OpenMP v4.5 Accelerator Model. The programmer can write a single application source file for the host and use OpenMP directives for parallelization and accelerator offloading. Lower-level details such as differing ISAs as well as shared virtual memory (SVM) between host and accelerator are handled by our heterogeneous toolchain based on LLVM 9, runtime libraries, kernel driver, and our open-source hardware IPs.

This repository contains the top-level logic and is the entry point to the HERO infrastructure. All dependencies and the board images or simulation setups can be built from here. HERO aims to offer a complete solution with minimum prerequisites.

## Getting Started

### Prerequisites
All build steps should work on any sufficiently recent Linux distribution (we have automated tests on CentOS 7). Most of the core dependencies are installed automatically as part of the toolchain. Required is at least GCC 4.8 / Clang 3.3 to bootstrap the toolchain installation.
More details can be found [here](PREREQUISITES.md).

### External sources
HERO uses Git submodules that have to be initialized. Either clone the repository recursively using
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
We recommend you create an `install` subdirectory in this repository and set `HERO_INSTALL` to that.

### Toolchains

HERO has configurations for multiple base toolchains. The project relies on Crosstool-NG for easily building the different toolchains. The toolchains are installed to the `HERO_INSTALL` directory.

All heterogeneous installations require a toolchain for the PULP accelerator, which can be built with:
```
make tc-pulp
```

Furthermore, both Linux and bare-metal toolchains are available for both the RISC-V Ariane host and for the ARMv8 Cortex-A53 host. These can be separately build as follows:
```
make tc-hrv-obare   # 64-bit RISC-V bare-metal toolchain
make tc-hrv-olinux  # 64-bit RISC-V Linux toolchain
make tc-har-obare   # 64-bit AArch64 bare-metal toolchain
make tc-har-olinux  # 64-bit AArch64 Linux toolchain
```
Current setups require only the Linux toolchains (`-olinux` suffix).

### PULP SDK
The PULP SDK is required to build applications for PULP. This has to be set up before installing the HERO host SDKs because support libraries rely on it. The required configuration can be built with
```
make sdk-pulp
```

### Host SDKs
Host Software Development Kits (SDKs) for both RISC-V and ARMv8 are necessary for the infrastructure of further build steps, for the development of heterogeneous applications, and for development on the HERO software stack itself. The SDKs are generated using Buildroot and installed to the `HERO_INSTALL` directory. These SDKs can be built as follows:
```
make sdk-hrv  # SDK for RISC-V host
make sdk-har  # SDK for ARMv8 host
```

### Heterogeneous Toolchain
After the base toolchains and accelerator and host SDKs are installed, the HERO heterogeneous toolchain can be installed. The heterogeneous toolchain is based on LLVM9 and includes support in Clang and OpenMP to create heterogeneous applications for the HERO target platform. The toolchain will be installed in the `HERO_INSTALL` toolchain folder together with the core toolchains and SDKs. To build and install the LLVM toolchain, run:
```
make tc-llvm
```
Note that the LLVM OpenMP target offloading plugin for PULP (i.e., `libomptarget.rtl.pulp.so`) is *not* compiled as part of LLVM.  Instead, it is compiled as package in the Host SDK, because it must be compiled for a specific Host architecture.  You can thus safely ignore the message `LIBOMPTARGET: Not building PULP offloading plugin: build disabled.`.

### Environments
With the toolchains and SDKs installed, several development environments can be created. At the moment HERO supports two different hardware targets: (1) a fully open-source FPGA implementation with a RISC-V Ariane host and (2) an implementation with a hard-macro ARMv8 Cortex-A on the Xilinx ZCU102. Moreover, elementary simulation targets are available for (1) the RISC-V host infrastructure using QEMU and (2) the PULP accelerator in an RTL simulator (QuestaSim).

##### Digilent Genesys 2
*NOTE: A complete FPGA bitstream for this platform is currently not available for external distribution yet*

A complete Linux environment with kernel and the base root filesystem for the Digilent Genesys 2 environment can be built with:
```
make br-hrv-ediggenesys2
```
The final product of this is a binary `hrv-ediggenesys-base-bbl.bin` in the `output` folder. This binary has to be put on an SD card to be loaded on the board. This SD card needs to be initialized with a GPT (GUID partition table). Be *CAREFUL* to execute the following steps on the correct partition and device (the SD card).
```
# fdisk -l # search for the disk label of the SD card (e.g. /dev/sdx)
# sgdisk --clear --new=1:2048:67583 --new=2 --typecode=1:3000 --typecode=2:8300 /dev/sdx # create a new gpt partition table and two partitions: 1st partition: 32mb (ONIE boot), second partition: rest (Linux root)
```
The system binary can then be copied onto the SD card using the disk partition created before, be *CAREFUL* again not to overwrite the wrong device:
```
# dd if=output/hrv-ediggenesys-base-bbl.bin of=/dev/sdx1 status=progress oflag=sync bs=1M
```
Once the FPGA bitstream is programmed correctly and the SD card is put in, the system can be booted. To develop applications for this setup, the dynamic environment can be loaded using `source env/ediggenesys2.sh`. Afterwards applications can be built and transferred directly to the board.

Currently the default MAC address is not loaded from the device, but fixed in the bitstream instead. It should be changed to allow for different devices on the same network. To achieve this, the system configuration can be customized by adding a single line with value `BR2_PACKAGE_ARIANE_SUPPORT_ETH_MAC="<custom-mac>"` to a file `local.cfg` in the root repository (create it if it does not yet exist). After changing this configuration parameter, the Ariane support package needs to be rebuilt with `make -C output/br-hrv-ediggenesys2 ariane-support-dirclean` followed by `make br-hrv-ediggenesys2`.

As on Ariane loading images from the SD card is currently limited and the root filesystem is not preserved on reboots, the base image does not directly contain the entire HERO infrastructure. A development filesystem based on the corresponding host SDK can be mounted externally instead. It is recommended to mount these images via NFS, the target filesystem can be extracted from `output/hrv-rootfs.tar`. This filesystem can be mounted automatically on boot by adding a configuration line with value `BR2_HERO_EXT_MOUNT="<mount-options> <ip>:<path>"` in `local.cfg` and then updating the image as above.

##### Xilinx ZCU102
A complete Linux environment with kernel and the base root filesystem for the ARMv8 host on the Xilinx Zynq UltraScale+ MPSoC ZCU102 can be built with:
```
make br-har-exilzcu102
```
This generates a SD card image containing the complete infrastructure and fully ready to be booted directly. It can be loaded on a SD card as follows, but *CAREFUL* action is required to not overwrite the wrong device.
```
# fdisk -l # search for the disk label of the SD-card (e.g. /dev/sdx)
# dd if=output/har-exilzcu102-base-sdcard.img of=/dev/sdx status=progress oflag=sync bs=1M # write the image on the SD-card
```
The system can then be booted up after configuring the ZCU102 board jumpers to boot from the SD card.  The root filesystem mounted after boot is provided by PetaLinux.  It is loaded into memory during boot, and changes are not persisted to the SD card.  Furthermore, that root filesystem does not include the HERO libraries.  A persistent filesystem, which includes the HERO libraries, resides on the second partition of the SD card.  We recommend mounting it at `/mnt`
```sh
mount /dev/mmcblk0p2 /mnt
```
and using its dynamically-linked shared libraries through
```sh
export LD_LIBRARY_PATH=/mnt/usr/lib:/mnt/lib
```
in every session on the board.  You may also want to place your binaries and data under `/mnt` to not lose them on a reboot (or kernel panic).

To develop applications for this setup, the dynamic environment on the development machine can be loaded using `source env/exilzcu102.sh`. Afterwards applications can be built and transferred directly to the board.

The host processor is implemented as a hard-macro, allowing the FPGA implementation of the accelerator to be loaded later during boot. A bitstream with the hardware implementation can be loaded automatically by adding `BR2_HERO_BITSTREAM=<path_to_bitstream>` in `local.cfg` and rebuilding the image with `make br-har-exilzcu102`.

##### QEMU RISC-V
For host debugging it can be useful to test the environment first with the QEMU machine emulator. A clone of the RISC-V Ariane environment without specific hardware patches and including virtual drivers can be built with:
```
make br-hrv-eqemu
```
A recent version of QEMU is required to be able to emulate RISC-V, it is currently recommended to build it from [source](https://github.com/qemu/qemu). After installation the following configuration can be used to boot:
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
An environment is provided to simulate the PULP accelerator in RTL. If QuestaSim is installed, the simulation infrastructure can be initialized as follows:
```
cd hardware
make
cd vsim
./compile.sh
```

For building applications for the simulation, the dynamic environment can be loaded with `source env/esim.sh`. When building OpenMP applications, it has to be specified to build them only for PULP using `make only=pulp`, which will also generate SLM files to initialize memory in simulation. Afterwards, the binary can be loaded in the simulator with:
```
cd hardware/vsim
../test/gen_slm_files.sh <app_name>
./start_sim.sh
```
where `<app_name>` is the path to the directory from the `openmp-examples` directory (for example `polybench-acc/2mm`).

### Tools
For development with RISC-V hardware the OpenOCD debugger can be useful. To simplify installation a target is provided that installs the debugger automatically to the `HERO_INSTALL` toolchain installation directory using
```
make tools-hrv-openocd
```
