puts "${Green}Analyzing apb_interrupt_cntrl ${NC}"

puts "${Green}--> compile apb_interrupt_cntrl${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/apb_interrupt_cntrl/apb_interrupt_cntrl.sv
