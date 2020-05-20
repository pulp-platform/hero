puts "${Green}Analyzing adv_dbg_if ${NC}"

puts "${Green}--> compile adv_dbg_if${NC}"
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/adv_dbg_if/rtl/adbg_axi_biu.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/adv_dbg_if/rtl/adbg_axi_module.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/adv_dbg_if/rtl/adbg_lint_biu.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/adv_dbg_if/rtl/adbg_lint_module.sv
analyze -format verilog   -define TARGET_SYNTHESIS -work work ${IPS_PATH}/adv_dbg_if/rtl/adbg_crc32.v
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/adv_dbg_if/rtl/adbg_or1k_biu.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/adv_dbg_if/rtl/adbg_or1k_module.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/adv_dbg_if/rtl/adbg_or1k_status_reg.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/adv_dbg_if/rtl/adbg_top.sv
analyze -format verilog   -define TARGET_SYNTHESIS -work work ${IPS_PATH}/adv_dbg_if/rtl/bytefifo.v
analyze -format verilog   -define TARGET_SYNTHESIS -work work ${IPS_PATH}/adv_dbg_if/rtl/syncflop.v
analyze -format verilog   -define TARGET_SYNTHESIS -work work ${IPS_PATH}/adv_dbg_if/rtl/syncreg.v
analyze -format verilog   -define TARGET_SYNTHESIS -work work ${IPS_PATH}/adv_dbg_if/rtl/adbg_tap_top.v
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/adv_dbg_if/rtl/adv_dbg_if.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/adv_dbg_if/rtl/adbg_axionly_top.sv
analyze -format sverilog  -define TARGET_SYNTHESIS -work work ${IPS_PATH}/adv_dbg_if/rtl/adbg_lintonly_top.sv
