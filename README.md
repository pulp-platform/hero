

This repository contains the software stack of HerOccamy for the AMD OpenHW Competition 2023.

It requires the HerOccamy FPGA flatform that can be found on [Github](https://github.com/pulp-platform/snitch/tree/master/hw/system/occamy/fpga).



# How to use HerOccamy

## Linux

Before all, you will need to compile a GCC RISCV64 toolchain, OpenSBI, U-boot and Linux, everything is taken care of by buildroot but it needs the device tree as an input. The device tree is located in the [Snitch](https://github.com/pulp-platform/snitch/) repository.

Clone Snitch and come back in the Hero repository.

First build the GCC toolchain and boot images.

```bash
# Setup the installation directory
mkdir install
export HERO_INSTALL=`pwd`/install
# Set HERO_DEVICE_DTS with the device tree
export HERO_DEVICE_DTS=<path_to_snitch>/hw/system/occamy/fpga/bootrom/occamy.dts
# Make rv64 toolchain, Linux, and others
make br-hrv-occamy
```

You can now add the `riscv64-hero-linux-` to your path:

```bash
export PATH=$HERO_INSTALL/share:$HERO_INSTALL/bin:$PATH
```

You can find the buildoot config in `configs/hrv_occamy_defconfig`, linux/busybox patches and config in `board/occamy` and the linux file system overlay in `board/common`.

__Attention:__ Right now U-Boot is configured to fetch the linux image via TFTP, edit the address in CONFIG_BOOTCOMMAND in `board/occamy/patches/u-boot-v2021.07/0001-WIP-Occamy-U-Boot-bringup.patch`, you could also edit this to boot from flash instead.

If you need to recompile uboot for instance :

```bash
cd output/br-hrv-occamy
# Recompile uboot
make uboot-dirclean uboot
cd ../..
# Recompile the Linux image
make br-hrv-occamy
```

Once compiled you find your images in in `output/br-hrv-occamy/images`.

In IIS you can use `make upload-linux-image` to send the images on the tftp server.

## Hardware

Now goto the snitch repository, follow the [README](https://github.com/pulp-platform/snitch/tree/hero-readmes/hw/system/occamy/fpga) there in `hw/system/occamy/fpga` and come back here.

## Boot

Connect to the FPGA's UART with Screen, once booted connect with `root` and no password.
You can not use the snitch cluster yet, there is an issue with OpenSBI wrongly setting up physical memory protection and restraining access to it. Start openOCD with the config in the Snitch repositoy. Connect GCC and set the correct PMP CSR : `set $pmpcfg0=0x1f1f18`.

You can set you ssh key on `board/common/overlay/root/.ssh/authorized_keys` for ssh access.

## Library and driver

Driver and library are located in `support/libsnitch` `support/snitch-driver`. The library is imported by applications to interact with the cluster and offload. Actual communication is handled by the driver through ioctl calls. The driver maps the physical addresses of the cluster to virtual addresses.

Both are compiled directly by buildroot. You can find out how in `package/libsnitch` `package/snitch-driver`. If you want to recompile them :

```bash
cd output/br-hrv-occamy
make snitch-driver-dirclean snitch-driver
make libsnitch-dirclean libsnitch
```
## LLVM toolchain

If you work on IIS machines, export the following environment variables for the correct compiler to build LLVM Toolchain
```bash
export CC=/usr/pack/gcc-9.2.0-af/linux-x64/bin/gcc
export CXX=/usr/pack/gcc-9.2.0-af/linux-x64/bin/g++
```

Install the LLVM tolchain for the Host and for Snitch by running:
```bash
make tc-llvm
make tc-snitch
```

Toolchains are compiled through scripts in the `toolchain/` directory.

If you have previously set the CC and CXX environment variables, unset them and then run:
```bash
unset CC
unset CXX
make sdk-snitch
```

This command vendored the snRuntime (with patches) in `vendor`, and compiled it in the `output/` directory.

You can explore the snRuntime in `vendor/snitch/sw`.

You can now offload applications! Goto `apps/hero-snitch/standalone/README.md`.

## OpenMP

Libomptarget is compiled by buildroot as well (`package/hero-openmp`)!

You can now compile your application :
Goto `hero-occamy/apps/hero-snitch/omp/README.md`.

Find the OpenMP runtime for Hero in `toolchain/llvm-project/openmp/libomptarget/plugins/hero`, find custom LLVM passes in `toolchain/llvm-support`.

## Common issues

Make sure that clang works by running `riscv32-unknown-elf-clang --version`, in case of error `version GLIBCXX_3.4.21 not found` it is possible that buildroot overwrote some libraries. Please re-run `make tc-llvm tc-snitch` to re-write these (should be fast).

## Licenses

Note this project uses [O(1) heap](https://github.com/pavel-kirienko/o1heap), a highly deterministic constant-complexity memory allocator designed for hard real-time high-integrity embedded systems. MIT license can be found in `support/libsnitch/vendor/o1heap/LICENSE`. 

For the licensing of the  remainder of the HERO project, see `LICENSE`.
