puts "${Green}Analyzing fpnew ${NC}"

puts "${Green}--> compile fpnew${NC}"
analyze -format sverilog  -work work ${IPS_PATH}/fpnew/src/fpnew_pkg.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpnew/src/fpnew_cast_multi.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpnew/src/fpnew_classifier.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpnew/src/fpnew_divsqrt_multi.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpnew/src/fpnew_fma.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpnew/src/fpnew_fma_multi.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpnew/src/fpnew_noncomp.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpnew/src/fpnew_opgroup_block.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpnew/src/fpnew_opgroup_fmt_slice.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpnew/src/fpnew_opgroup_multifmt_slice.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpnew/src/fpnew_rounding.sv
analyze -format sverilog  -work work ${IPS_PATH}/fpnew/src/fpnew_top.sv
