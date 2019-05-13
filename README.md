# HERO-V3

HERO-V3, the open Heterogeneous Research Platform version 3, combines a PULP-based open-source parallel manycore accelerator implemented on FPGA with a hard open-source Ariane host processor running full-stack Linux.

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

The project contains several toolchains for various configurations. First the basic Linux Ariane toolchain with recent version of several host tools included (necessary for building the tools) can be built with
```
make toolchain-ariane-linux
```

For a full-blown HERO installation the PULP toolchain is required together with an extended version of the Linux toolchain, which can be built with
```
make toolchain-ariane-hero
make toolchain-pulp
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
Complete Linux environment with kernel and filesystem are built using Buildroot, which uses the cross-compilation toolchain to build for the platform. 

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
On the Ariane hardware the environment can be chrooted via NFS instead. 
