# Hardware
Contains all the open-source hardware involved in HERO. The hardware is managed by [bender](https://github.com/fabianschuiki/bender) for which a recent version can be installed by running `make` in this directory.

## Simulation
To initialize RTL simulation, the hardware should be compiled by running `vsim/compile.sh`. Hereafter a heterogeneous application could be run in simulation as follows:
* Move to a subdirectory of `openmp-examples` with a heterogeneous application (for example `openmp-examples/polybench-acc/2mm`).
* (Re)build the application in standalone mode with `make only=pulp clean all`.
* Goto `hardware/test` and generate teh appropriate files with `./gen_slm_files.sh` with the path to the heterogeneous application after `openmp-examples` (for example `./gen_slm_files.sh polybench-acc/2mm`).
* Start the simulation of the application by going to the `vsim` directory and running `./start_sim.sh`.
