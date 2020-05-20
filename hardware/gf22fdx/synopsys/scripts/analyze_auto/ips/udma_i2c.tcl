puts "${Green}Analyzing udma_i2c ${NC}"

puts "${Green}--> compile udma_i2c${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_i2c/rtl/udma_i2c_reg_if.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_i2c/rtl/udma_i2c_bus_ctrl.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_i2c/rtl/udma_i2c_control.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/udma/udma_i2c/rtl/udma_i2c_top.sv
