# initialize default optional parameters
set_if_undef CLKNAME clk_i
set_if_undef TI [expr 0.1*$TCK]
set_if_undef TO [expr 0.1*$TCK]

# basic main clock constraints
create_clock -period ${TCK} [get_ports ${CLKNAME}]
set_input_delay ${TI} [remove_from_collection [all_inputs] ${CLKNAME}] -clock ${CLKNAME}
set_output_delay ${TO} [all_outputs]  -clock ${CLKNAME}

