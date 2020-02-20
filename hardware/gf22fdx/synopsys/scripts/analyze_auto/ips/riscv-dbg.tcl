puts "${Green}Analyzing riscv-dbg ${NC}"

puts "${Green}--> compile riscv-dbg${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/riscv-dbg/src/dm_pkg.sv
analyze -format sverilog  -work work ${IPS_PATH}/riscv-dbg/debug_rom/debug_rom.sv
analyze -format sverilog  -work work ${IPS_PATH}/riscv-dbg/src/dm_csrs.sv
analyze -format sverilog  -work work ${IPS_PATH}/riscv-dbg/src/dm_mem.sv
analyze -format sverilog  -work work ${IPS_PATH}/riscv-dbg/src/dm_top.sv
analyze -format sverilog  -work work ${IPS_PATH}/riscv-dbg/src/dmi_cdc.sv
analyze -format sverilog  -work work ${IPS_PATH}/riscv-dbg/src/dmi_jtag.sv
analyze -format sverilog  -work work ${IPS_PATH}/riscv-dbg/src/dmi_jtag_tap.sv
analyze -format sverilog  -work work ${IPS_PATH}/riscv-dbg/src/dm_sba.sv
