# Boards
Currently the targeted platforms are:
* Digilent Genesys II with an Ariane RISC-V host
* Xilinx ZCU102 with an ARMv8 host
And finally there is an elementary simulation setup for 
* QEMU standalone with a RISC-V host (no PULP)

This folder contains the configuration for these boards
* common: common base configuration for all targets
* qemu: simulation configuration for QEMU
* hero: configuration for heterogeneous applications in the HERO platform
* rv: RISC-V (Ariane) specific configuration
* exildiggenesys2: configuration for the Genesys II board (execution environment)
* exilzcu102: configuration for the ZCU102 board (execution environment)
