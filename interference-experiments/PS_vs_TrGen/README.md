# PS vs PL Traffic Generator Experiments

This folder contains scripts and binaries for the Arm host processor.  Make sure
the traffic generator image is deployed on the board before executing these
scripts.

Each script iterates over different benchmark applications running on the APU
and configurations of the traffic generators on the PL.

In `run_tg_pi.sh`, the traffic generators are the primary interferers.  This
script goes together with the `.elf` files *without* `_noise` suffix.

In `run_tg_put.sh`, the traffic generators are the program under test.  This
script goes together with the `.elf` files *with* `_noise` suffix.

Copy the `.elf` files to the board and adapt the `EXPERIMENT_BENCHMARK_PATH` in
both `.sh` scripts accordingly.

The results reported by the scripts are TODO.
