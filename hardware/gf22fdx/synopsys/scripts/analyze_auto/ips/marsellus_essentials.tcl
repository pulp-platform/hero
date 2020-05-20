puts "${Green}Analyzing marsellus_essentials ${NC}"

puts "${Green}--> compile quentin_essentials${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/marsellus_essentials/pad_frame_gf22.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/marsellus_essentials/memwrap.sv

