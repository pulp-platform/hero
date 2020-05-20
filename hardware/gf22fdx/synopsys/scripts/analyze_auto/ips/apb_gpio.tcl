puts "${Green}Analyzing apb_gpio ${NC}"

puts "${Green}--> compile apb_gpio${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/apb/apb_gpio/./rtl/apb_gpio.sv
