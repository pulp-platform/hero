# HERO-V3

HERO-V3, the open Heterogeneous Research Platform version 3, combines a PULP-based open-source parallel manycore accelerator with an open-source Ariane host processor running full-stack Linux.

This repository contains the top-level logic to build all required dependencies.

## Getting Started

### Prerequisites
The build should work on any sufficiently recent Linux version (only tested is CentOS 7 until now). Most of the core dependencies are installed automatically as part of the toolchain. Required is at least GCC 4.8 / Clang 3.3 to bootstrap the toolchain installation.

### Sources
HERO-V3 uses Git submodules. Either clone the repository recursively using
```
git clone --recursive <url>
```
or fetch the submodules afterwards in the repository
```
git submodule update --init --recursive
```

### Toolchain
All toolchains are installed automatically to the location pointed to by the `RISCV` environment variable. Please set it to your preferred installatation location before continueing with the next step
```
export RISCV=<your_path>
```

The project contains several toolchains for various configurations. The core Linux Ariane toolchain with recent version of several host tools included (necessary for building the tools) is required first and can be built with
```
make tc-ariane-linux
```

For a full HERO installation the PULP toolchain is also required, which can be built with
```
make tc-pulp
```

### Tools
For development with RISCV-V the Spike ISA simulator tool and the OpenOCD debugger are useful. These can be installed as follows (after the toolchain is built) and are installed automatically to the `RISCV` toolchain installation directory
```
make tools
```

### Hardware
The FPGA bitstream for the Genesys II board can be generated with Vivado using
```
make hw-ariane
```

The output files (ariane\_xilinx.mcs) can be found in `hardware/ariane/fpga/work-fpga`. The process to programmed the device is described in the documentation of the [Ariane](https://github.com/pulp-platform/ariane#programming-the-memory-configuration-file) repository.

### PULP SDK
For building applications for PULP, the PULP-SDK is required. This has to be set-up before installing the HERO environment as support libraries rely on it. The required configuration can be built with
```
make pulp-sdk
```

### Environment
A complete Linux environment with kernel and filesystem is built using Buildroot, which uses the cross-compilation toolchain to build for the platform. 

The environment is typically created from upstream repositories, but it is possible to overwrite the code source to be used. This can be done by creating and modifying a `local.mk` file in the root folder of the repository. Package sources can then be overwritten by adding a line with `<PACKAGE>_OVERRIDE_SRCDIR=<location>`. 

**Currently two packages are required to have a overwritten source directory as the upstream versions are outdated. To achieve this clone `git@iis-git.ee.ethz.ch:kwolters/hero-support.git` and `git@iis-git.ee.ethz.ch:kwolters/libhero-target.git`, and add a `HERO_SUPPORT_OVERRIDE_SRCDIR` and `LIBHERO_TARGET_OVERRIDE_SRCDIR` pointing to the appropriate location of the sources.**

#### Ariane
A ready-to-use image for standalone Ariane can be created first with
```
make br-ariane
```
This creates a binary `bbl.bin` in the main folder. To put it on a SD-card first a GPT partition table is required to be created (this step is needed only once). Be *CAREFUL* to execute the following steps on the correct partition and device (the SD-card).
```
$ sudo fdisk -l # search for the corresponding disk label (e.g. /dev/sdb)
$ sudo sgdisk --clear --new=1:2048:67583 --new=2 --typecode=1:3000 --typecode=2:8300 /dev/sdb # create a new gpt partition table and two partitions: 1st partition: 32mb (ONIE boot), second partition: rest (Linux root)
```
The binary can the be copied onto the SD-card using the same disk label found before, be *CAREFUL* again not to overwrite the wrong device:
```
$ sudo dd if=bbl.bin of=/dev/sdb1 status=progress oflag=sync bs=1M
```
If the FPGA bitstream is programmed correctly and the SD-card is put in, the system can now be booted up!

Currently the default MAC address is fixed in the bitstream and should be changed later to allow for different devices on the same network. To achieve this the Ariane buildroot configuration can be customized by adding a single line with value `BR2_PACKAGE_ARIANE_SUPPORT_ETH_MAC="<custom-mac>"` to a file `local.cfg` in the root repository (create it if it does not yet exist). After changing this configuration parameter, the ariane support package needs to be rebuild, this can be achieved with `make -C output/br-ariane ariane-support-dirclean` and then rerunning `make br-ariane` from the top-level directory of the repository.

#### QEMU
For debugging it can be quite useful to test the environment first with the QEMU machine emulator. A clone of the Ariane environment without specific hardware patches and including virtual drivers instead, can be built with:
```
make br-qemu
```
The Linux image and filesystem are found in `output/qemu/images`, referred as `<image_directory>` below. A fairly recent version of QEMU is required to be able to emulate RISC-V, it is currently recommended to build it from source from [here](https://github.com/qemu/qemu). After installation the following configuration can be used to bootup
```
qemu-system-riscv64 \
   -machine virt -nographic \
   -kernel <image_directory>/bbl \
   -append "root=/dev/vda ro" \
   -drive file=<image_directory>/rootfs.ext2,format=raw,id=hd0 \
   -device virtio-blk-device,drive=hd0 \
   -netdev user,id=net0,hostfwd=tcp::5555-:22 \
   -device virtio-net-device,netdev=net0 \
   -device virtio-rng-device \
   -gdb tcp::3332

```
It it possible to SSH to the machine on port 5555 and debug with GDB on port 3332.

#### HERO
A larger complete HERO environment with more packages and support libraries can then be created via
```
make br-hero
```
It is possible the filesystem image from `output/hero/images/` (referred as `<hero_image_directory>` below) in QEMU by adding
```
   -drive file=<hero_image_directory>/rootfs.ext4,format=raw,id=hd1 \
   -device virtio-blk-device,drive=hd1 \
```
to the command to run above. Afterwards you can execute `chroot /mnt` to change to the HERO environment.
On the Ariane hardware the environment can be chrooted via NFS instead. To automate the mounting of an NFS filesystem on boot, a configuration line with value `BR2_PACKAGE_ARIANE_SUPPORT_EXT_MOUNT="<mount-options> <ip>:<path>"` can be specified in `local.cfg`.

### HERO-SDK
From the HERO buildroot image an external sdk can be generated and integrated in the `RISCV` toolchain installation. This SDK is required to compile heterogeneous applications with OpenMP. The SDK can be installed with
```
make hero-sdk
```

### LLVM OpenMP RTE
After the Ariane toolchain, the PULP toolchain, the PULP SDK and the HERO SDK are installed, the HERO LLVM RTE can be installed. This includes clang and OpenMP build support to create heterogeneous applications. It will be installed in the `RISCV` toolchain folder together with the other toolchain parts. To build and install the HERO LLVM setup, run:
```
make hero-llvm
```
