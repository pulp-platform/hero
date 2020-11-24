# basic main clock constraints
create_clock -period ${TCK} [get_ports ${CLKNAME}]
set_input_delay ${TI} [remove_from_collection [all_inputs] ${CLKNAME}] -clock ${CLKNAME}
set_output_delay ${TO} [all_outputs]  -clock ${CLKNAME}

