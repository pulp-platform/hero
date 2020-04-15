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

Open `gdb` now and and execute
```
target remote localhost:3333
```

You should now be able to load a binary and debug it.

