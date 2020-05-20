puts "${Green}Analyzing apb_fll_if ${NC}"

puts "${Green}--> compile apb_fll_if${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/apb/apb_fll_if/apb_fll_if.sv
