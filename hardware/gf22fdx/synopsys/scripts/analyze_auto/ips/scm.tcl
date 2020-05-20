puts "${Green}Analyzing scm ${NC}"

puts "${Green}--> compile scm${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/scm/latch_scm/register_file_1r_1w_test_wrap.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/scm/latch_scm/register_file_1w_64b_multi_port_read_32b_1row.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/scm/latch_scm/register_file_1w_multi_port_read_1row.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/scm/latch_scm/register_file_1r_1w_all.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/scm/latch_scm/register_file_1r_1w_all_test_wrap.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/scm/latch_scm/register_file_1r_1w_be.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/scm/latch_scm/register_file_1r_1w.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/scm/latch_scm/register_file_1r_1w_1row.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/scm/latch_scm/register_file_1w_128b_multi_port_read_32b.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/scm/latch_scm/register_file_1w_64b_multi_port_read_32b.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/scm/latch_scm/register_file_1w_64b_1r_32b.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/scm/latch_scm/register_file_1w_multi_port_read_be.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/scm/latch_scm/register_file_1w_multi_port_read.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/scm/latch_scm/register_file_2r_1w_asymm.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/scm/latch_scm/register_file_2r_1w_asymm_test_wrap.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/scm/latch_scm/register_file_2r_2w.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/scm/latch_scm/register_file_3r_2w.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/scm/latch_scm/register_file_3r_2w_be.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/scm/latch_scm/register_file_multi_way_1w_64b_multi_port_read_32b.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/scm/latch_scm/register_file_multi_way_1w_multi_port_read.sv

