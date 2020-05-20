puts "${Green}Analyzing udma_camera ${NC}"

puts "${Green}--> compile udma_camera${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_camera/rtl/camera_reg_if.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_camera/rtl/camera_if.sv
