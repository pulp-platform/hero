set_attribute [get_cells  $CLK_GATE_CELL  ] is_clock_gating_cell true

set_clock_gating_style -minimum_bitwidth 3 -positive_edge_logic integrated:$CLK_GATE_CELL -control_point  before  -control_signal scan_enable  -max_fanout 256

echo "Setting clock gating variables"
set compile_clock_gating_through_hierarchy true ;
set power_cg_balance_stages false ;
