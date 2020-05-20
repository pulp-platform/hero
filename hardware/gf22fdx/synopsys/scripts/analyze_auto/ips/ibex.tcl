puts "${Green}Analyzing ibex ${NC}"

puts "${Green}--> compile ibex${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/ibex/rtl/ibex_pkg.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/ibex/rtl/ibex_alu.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/ibex/rtl/ibex_compressed_decoder.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/ibex/rtl/ibex_controller.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/ibex/rtl/ibex_cs_registers.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/ibex/rtl/ibex_decoder.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/ibex/rtl/ibex_ex_block.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/ibex/rtl/ibex_id_stage.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/ibex/rtl/ibex_if_stage.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/ibex/rtl/ibex_load_store_unit.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/ibex/rtl/ibex_multdiv_slow.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/ibex/rtl/ibex_multdiv_fast.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/ibex/rtl/ibex_prefetch_buffer.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/ibex/rtl/ibex_fetch_fifo.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/ibex/rtl/ibex_pmp.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/ibex/rtl/ibex_core.sv


puts "${Green}--> compile ibex_regfile_rtl${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/ibex/rtl/ibex_register_file_latch.sv

