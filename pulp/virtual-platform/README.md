# PULP SDK builder


## About

This module is a simplified build process for the PULP SDK.

### GVSOC build

You need to first install the Linux dependencies (see [below](#dependencies)).

Choose the configuration for which you want to compile gvsoc, for example:

    $ source configs/gap_rev1.sh

Then execute this script:

    $ ./scripts/build-gvsoc

You can open install/doc/vp/index.html to see the documentation.

To use it, first source this file, this will put all install files in the `PATH`:

    $ source setup.sh

Then you can go to examples/fork/gap_rev1 and execute:

    $ pulp-run --platform=gvsoc --config=gap_rev1 --binary=test prepare run

### Runtime build

You need to first install the Linux dependencies (see [below](#dependencies)).

Choose the configuration for which you want to compile the runtime, for example:

    $ source configs/gap_rev1.sh

Then execute this script:

    $ ./scripts/build-runtime

To use it, first source this file, this will put all install files in the `PATH`:

    $ source sdk-setup.sh

Then you can get one of the pulp example, compile and run it.


## Linux dependencies

Here are the required system dependencies for building the SDK and its dependencies.

### Ubuntu 16.04

Starting from a fresh Ubuntu 16.04 distribution, here are the commands to be executed to get all required dependencies:

    $ sudo apt install git python3-pip gawk texinfo libgmp-dev libmpfr-dev libmpc-dev swig3.0 libjpeg-dev lsb-core doxygen python-sphinx sox graphicsmagick-libmagick-dev-compat libsdl2-dev libswitch-perl libftdi1-dev cmake scons libsndfile1-dev
    $ sudo pip3 install twisted prettytable pyelftools openpyxl xlsxwriter pyyaml numpy configparser pyvcd
    $ sudo pip2 install configparser

### Scientific Linux 7.4

Starting from a fresh Scientific Linux 7.4 distribution, here are the commands to be executed to get all required dependencies:

    $ sudo yum install git python34-pip python34-devel gawk texinfo gmp-devel mpfr-devel libmpc-devel swig libjpeg-turbo-devel redhat-lsb-core doxygen python-sphinx sox GraphicsMagick-devel ImageMagick-devel SDL2-devel perl-Switch libftdi-devel cmake scons
    $ sudo pip3 install twisted prettytable pyelftools openpyxl xlsxwriter pyyaml numpy configparser pyvcd
    $ sudo pip2 install configparser

## Dependencies

### Build

Have a look at the dependencies documentation to see how to build them.

You can have a look [here](https://github.com/pulp-platform/pulp-riscv-gnu-toolchain.git) for the toolchain.

### Setup

All the dependencies required to build the SDK must be setup through environment variables.

The toolchain must be built separately and the following environment variable should 
point to it:

    $ export PULP_RISCV_GCC_TOOLCHAIN=<path to the folder containing the bin folder of the toolchain>

RTL platforms should also be built separately (see the platform documentation for that) and the following
environment variable must point to the folder where the platform was installed (this example is for pulpissimo):

    $ export VSIM_PATH=<pulpissimo root folder>/sim

