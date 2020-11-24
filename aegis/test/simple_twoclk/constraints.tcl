# clk_i
create_clock -period 10 [get_ports clk_i]
set_input_delay 2 {a a_valid_i b} -clock clk_i
set_output_delay 2 {a_ready_o z_bb}  -clock clk_i

# clk_ext
create_clock -period 6.67 [get_ports clk_ext_i]
set_input_delay 1 {z_ready_i} -clock clk_ext_i
set_output_delay 1 {z z_valid_o}  -clock clk_ext_i

# CDC
set asyncs_src [get_pins i_cdc_fifo_gray/i_src/async_*]
set asyncs_dst [get_pins i_cdc_fifo_gray/i_dst/async_*]
set_ungroup [get_designs cdc_fifo_gray*] false
set_boundary_optimization [get_designs cdc_fifo_gray*] false
set_max_delay 6.67 -through $asyncs_src -through $asyncs_dst
set_false_path -hold -through $asyncs_src -through $asyncs_dst
