# Buildroot configuration
Buildroot configuration files for different execution environments as well as generic architecture specific embedded setups are available in this directory. 
These configurations are supposed to be invoked from the top-level `Makefile`.
These files are generated from the following configuration:
* har\_defconfig: generic embedded filesystem for AArch64 (can for example be mounted via NFS)
* har\_exilzcu102\_defconfig: embedded execution environment for ZCU102 (currently relies on Vivado Petalinux to workaround a board issue)
* hrv\_defconfig: generic embedded filesystem for RISCV64 (can for example be mounted via NFS)
* hrv\_ediggenesys2\_defconfig: generic embedded filesystem for the Genesys II
* hrv\_eqemu\_defconfig: embedded filesystem for QEMU with virtual devices 
