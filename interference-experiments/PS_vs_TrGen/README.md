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

To run the scripts on the ZCU102, the HERO root file system must include the zsh
shell and the bc calculator. This will be done by default if the system is built
as described in the top-level README.

The scripts produce one output file per PUT-PI pair, which contains all sampled
execution times for the PUT under that condition. The naming scheme of the
output files indicate:

For TG as PUT:
    TrafGenDump\_<TIME>\_<PI>\_<FREQ>MHz\_ops=<BURSTS>\_psvspl\_datadump.txt
    where TIME is the time the script was launched, PI is the interfering
    benchmark (above mentioned .elf files) or none for isolation, FREQ is the
    frequency of the traffic generator, and BURSTS is the number of bursts to be
    measured. Each burst accesses 4 KB. Each line in the file is a sample of the
    end-to-end latency for the traffic generator memory accesses.

For TG as PI:
    TrafGenDump\_<TIME>\_<PUT>\_<TGs>trafgen\_word3<QOS>\_datadump.txt
    where TIME is the time the script was launched, PUT is the benchmark whose
    times are measured (each line in the file is a sampled execution time of
    this benchmark), TGs is the number of traffic generators that are
    interfering (0 for isolation), and QOS is a somewhat cryptical value that
    determines the QoS settings for the traffic generator memory accesses. The
    QOS field for the low 0x0 priority is 0x30, and 0xF0030 for the high 0xF
    priority.

To produce the plots in the report, we co-plot the sampled data for the isolated
run (PI=none for TG as PUT, TGs=0 for TG as PI) and the other configurations in
a histogram.
