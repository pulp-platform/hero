# RISC-V Debug

You can interact with the RISC-V debug module of hero in a RTL simulation with
GDB. GDB can talk to OpenOCD which in turn talks to `librbs`. This DPI library
interfaces with a JTAG DPI bridge in the hero testbench.

This is _not_ a viable approach to debug software on the simulator, since it is
very slow.

## Configuring the Simulation
`librbs` should be automatically compiled when you use the `compile.sh` script.

The RTL model needs to be compiled with the JTAG DPI bridge enabled. You do this
by setting `VLOG_ARGS` accordingly:

```bash
cd vsim/
VLOG_ARGS=+define+USE_JTAG_DPI ./compile.sh
```

Now you can start the simulation with the DPI enabled run script
```bash
./start_sim_with_dpi.sh
```

## OpenOCD and GDB
Now the simulation will be waiting for OpenOCD to connect. You do this by calling
```
openocd -f your-openocd-script.cfg
```

Currently there are two scripts provided for debugging with GDB:
`test/dm_8pe_hwthread.cfg` and `test/dm_8pe_rtos_riscv.cfg`. Both allow
debugging all eight cores at once, but differ how openocd handles the cores:

* -rtos riscv (used in `dm_8pe_rtos_riscv.cfg`): Deprecated and only there for backwards
  compatibility reasons. Represent cores as threads in gdb, but the
  implementation is really hacky.
* -rtos hwthread (used in `dm_8pe_hwthread.cfg`): Represent cores as threads in gdb. See
  the [OpenOCD manual](http://openocd.org/doc/html/GDB-and-OpenOCD.html#Using-OpenOCD-SMP-with-GDB)
  for more details.

Finally open `gdb` and execute

```
target remote localhost:3333
```

You should now be able to load a binary and debug it.

## OpenOCD tests
OpenOCD has some internal tests that can be run. To run those, pass
`dm_compliance_test.cfg`. If you just want to quickly tests connectivity
(checking whether OpenOCD can interact with the hardware) use
`dm_connection_rtos_riscv_test.cfg` or `dm_connection_hwthread_test.cfg`.

