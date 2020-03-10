puts "${Green}Analyzing pulp_soc ${NC}"

analyze -format sverilog -work work ${IPS_PATH}/apb/src/apb_intf.sv

analyze -format sverilog -work work ${RTL_PATH}/apb/apb_bus.sv
analyze -format sverilog -work work ${RTL_PATH}/apb/apb_bus_wrap.sv
analyze -format sverilog -work work ${RTL_PATH}/apb/apb_ro_regs.sv
analyze -format sverilog -work work ${RTL_PATH}/apb/apb_rw_regs.sv
#analyze -format sverilog -work work ${RTL_PATH}/apb/apb_stdout.sv
analyze -format sverilog -work work ${RTL_PATH}/axi_rab_wrap.sv
analyze -format sverilog -work work ${RTL_PATH}/pulp_cluster_cfg_pkg.sv

analyze -format sverilog -work work ${RTL_PATH}/debug_system.sv
analyze -format sverilog -work work ${RTL_PATH}/l2_mem.sv
analyze -format sverilog -work work ${RTL_PATH}/pulp_cluster_ooc.sv
analyze -format sverilog -work work ${RTL_PATH}/soc_bus.sv
analyze -format sverilog -work work ${RTL_PATH}/soc_ctrl_regs.sv
analyze -format sverilog -work work ${RTL_PATH}/soc_peripherals.sv
analyze -format sverilog -work work ${RTL_PATH}/sram.sv

analyze -format sverilog -work work ${RTL_PATH}/pulp.sv
analyze -format sverilog -work work ${RTL_PATH}/pulp_ooc.sv
analyze -format sverilog -work work ${RTL_PATH}/core2axi.sv
analyze -format sverilog -work work ${RTL_PATH}/axi_tcdm_if.sv
