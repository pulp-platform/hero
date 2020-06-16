# Hemera: Integrating a PULP Cluster With a Microcontroller Host Processor Using the HERO Framework

This variant of HERO provides the hardware and software to integrate PULP with a simple microcontroller host processor.

## Repository Organization

- `doc` contains the datasheet.
- `example-apps` contains example applications and tests for PULP.
- `hardware` contains RTL source code and scripts to simulate and synthesize PULP.
- `pulp` contains system software for PULP.
- `toolchain` contains the configuration to build the PULP toolchain.

## Getting Started

### Prerequisites

All build steps should work on any sufficiently recent Linux distribution (we have automated tests on CentOS 7).  Most of the core dependencies are installed automatically as part of the toolchain.  Required is at least GCC 4.8 / Clang 3.3 to bootstrap the toolchain installation.
More details can be found [here](PREREQUISITES.md).

### Setup

The toolchain is installed to the directory given by your `HERO_INSTALL` environment variable. Please set it to your preferred installation location before continuing with the next step
``` bash
export HERO_INSTALL=<your_path>
```
We recommend you create an `install` subdirectory in this repository and set `HERO_INSTALL` to that.

After that, simply execute the `setup.sh` script to build the PULP toolchain.

## Compilation

### Environments

Compilation always requires a proper environment. When compiling with the minimal runtime `source env/ehuawei-minimal-runtime.sh`. For the full SDK use `source env/esim.sh`

### Applications

The `example-apps` folder contains different example applications, which are supposed to be used with different environments.

- **Minimal runtime (`source env/ehuawei-minimal-runtime.sh`):**
  + hello
  + mchan_tests
  + parMatrixMul
- **Pulp SDK (`source env/esim.sh`):**
  + helloworld
  + tests-pulp

Run `make` in an application directory to build it, e.g., in `example-apps/hello`.

## RTL Simulation

### QuestaSim

An environment is provided to simulate the PULP accelerator in RTL. If QuestaSim is installed, the simulation infrastructure can be initialized as follows:
``` bash
cd hardware/vsim
./compile.sh
```

Then, generate SLM files to initialize memory with
``` bash
../test/gen_slm_files.sh <app_name>
```
where `<app_name>` is the path to the directory from the `example-apps` directory (for example `hello`).

Finally, start the simulation with
```
./start_sim.sh
```

### VCS

The repository also includes VCS scripts for simulation. However, the VCS scripts are not as mature as the QuestaSim scripts:
``` bash
cd hardware/vcs
./compile.sh
```

Then, generate SLM files to initialize memory with
``` bash
../test/gen_slm_files.sh <app_name>
```
where `<app_name>` is the path to the directory from the `example-apps` directory (for example `hello`).

Finally, start the simulation with
``` bash
./start_sim.sh
```

## Virtual Platform

Build the virtual platfrom by executing `make virtual-platform` in the repository's root directory.

To launch an application use the `run_vp.sh` script in the `pulp/virual-platform` repository. It takes the name of an application or the full path to a binary as an argument. For example to launch the `hello` application use:
``` bash
./pulp/virual-platform/run_vp.sh hello
```

The script contains two configuration variables.
- `out_dir`: Contains the path to the output logs of the virtual platform.
- `trace`: Indicates which events should be logged and to which files they should be written.

By default, the instruction trace of all cores is written to `pulp/virtual-platform/output/cluster`.
