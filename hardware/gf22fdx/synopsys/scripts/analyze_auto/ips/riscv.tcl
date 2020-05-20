puts "${Green}Analyzing riscv ${NC}"

puts "${Green}--> compile riscv_regfile_rtl${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/register_file_test_wrap.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/riscv_register_file_latch.sv

puts "${Green}--> compile riscv${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/include/apu_core_package.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/include/riscv_defines.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/include/riscv_tracer_defines.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/riscv_alu.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/riscv_alu_basic.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/riscv_alu_div.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/riscv_compressed_decoder.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/riscv_controller.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/riscv_cs_registers.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/riscv_decoder.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/riscv_int_controller.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/riscv_ex_stage.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/riscv_hwloop_controller.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/riscv_hwloop_regs.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/riscv_id_stage.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/riscv_if_stage.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/riscv_load_store_unit.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/riscv_mult.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/riscv_prefetch_buffer.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/riscv_prefetch_L0_buffer.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/riscv_core.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/riscv_apu_disp.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/riscv_fetch_fifo.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/riscv_L0_buffer.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/riscv/./rtl/riscv_pmp.sv




