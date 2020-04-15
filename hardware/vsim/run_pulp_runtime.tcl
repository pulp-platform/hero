source run_common_pre.tcl

eval "vsim -voptargs=\"+acc\" -t 1ps -warning 3009 $vsimFlagsTcl pulp_tb"

if { ! [batch_mode] } {
    source pulp_tb.wave.do
}

source run_common_post.tcl
