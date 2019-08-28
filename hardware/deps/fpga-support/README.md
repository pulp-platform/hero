# IP Blocks to Support Design, Prototyping, and Verification of PULP on FPGAs

This repository contains IP blocks that can be useful in many aspects of working with PULP on FPGA
platforms.  The repository is structured as follows:

- `behav/`  Behavioral Simulation and Tests; contains one subdirectory for each module.
- `rtl/`    End-User RTL Code
- `synth/`  Post-Synthesis Simulation and Tests; contains one subdirectory for each module.

## Usage

Many IP blocks in this repository depend on `cf_math_pkg` from `common_cells`.  Make sure to elaborate
`cf_math_pkg` before the IP blocks in this repository.

Add all files in the `rtl/` folder to the list of compilation files of your development tool (e.g.,
Xilinx Vivado).  Read the documentation (header of the source file) of the block that you want to
use and use the block as described there.

## Contributing

Thank you for your intent to contribute to improving the quality and usefulness of this repository!
In the interest of making this an optimal experience for you, the maintainers, and the users, please
follow the [Contribution Guidelines](CONTRIBUTING.md)
