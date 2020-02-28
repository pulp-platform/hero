#FLL Routing blk

createRouteBlk -box [expr $init_Xfll + $fllSize_W - 3.5 ] \
[expr $init_Yfll - $routingFLL ] \
[expr $init_Xfll + $fllSize_W + 4.85 ] [expr $init_Yfll + $fllSize_H + $routingFLL + 0.5 ] -layer C5

createRouteBlk -box [expr $init_Xfll + 2*$fllSize_W - 2.7 ] \
[expr $init_Yfll - $routingFLL ] \
[expr $init_Xfll + 2*$fllSize_W + 5.85 ] [expr $init_Yfll + $fllSize_H + $routingFLL + 0.5 ] -layer C5


#VBN VBP (M7) - memories

#Mem Columns Left
addStripe -nets {VDD_ARR VDD_PER VSS} -layer C5 -direction vertical -width 0.34 -spacing 2 -set_to_set_distance 10 \
-area {2.3 1153.75 297.4 1.5} -start_from left -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 -use_wire_group 0 \
-snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

addStripe -nets {VNW_N VPW_P} -layer C5 -direction vertical -width 0.17 -spacing 1 -set_to_set_distance 10 \
-area {9.32 1153.75 297.4 1.5} -start_from left -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 -use_wire_group 0 \
-snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

#Mem Columns Right

addStripe -nets {VDD_ARR VDD_PER VSS} -layer C5 -direction vertical -width 0.34 -spacing 2 -set_to_set_distance 10 \
-area {1542.87 975.82 1837.35 1.5} -start_from left -switch_layer_over_obs false -max_same_layer_jog_length 2 -padcore_ring_top_layer_limit LB \
-padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 -use_wire_group 0 -snap_wire_center_to_grid None \
-skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

addStripe -nets {VNW_N VPW_P} -layer C5 -direction vertical -width 0.17 -spacing 1 -set_to_set_distance 10 \
-area {1549.89 975.82 1837.35 1.5} -start_from left -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 -use_wire_group 0 \
-snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

#Mem in the middle, two speps as it is not regular shape

addStripe -nets {VDD_ARR VDD_PER VSS} -layer C5 -direction vertical -width 0.34 -spacing 2 -set_to_set_distance 10 \
-area {625.10 356.73 1074.82 1.5} -start_from left -switch_layer_over_obs false -max_same_layer_jog_length 2 -padcore_ring_top_layer_limit LB \
-padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 -use_wire_group 0 -snap_wire_center_to_grid None \
-skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

addStripe -nets {VNW_N VPW_P} -layer C5 -direction vertical -width 0.17 -spacing 1 -set_to_set_distance 10 \
-area {632.12 356.73 1074.82 1.5} -start_from left -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 -use_wire_group 0 \
-snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

addStripe -nets {VDD_ARR VDD_PER VSS} -layer C5 -direction vertical -width 0.34 -spacing 2 -set_to_set_distance 10 \
-area {1076.82 267.26 1215.28 1.5} -start_from left -switch_layer_over_obs false -max_same_layer_jog_length 2 -padcore_ring_top_layer_limit LB \
-padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 -use_wire_group 0 -snap_wire_center_to_grid None \
-skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

addStripe -nets {VNW_N VPW_P} -layer C5 -direction vertical -width 0.17 -spacing 1 -set_to_set_distance 10 \
-area {1083.84 267.26 1215.28 1.5} -start_from left -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 -use_wire_group 0 \
-snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

#FLL



#Delete routing blk from FLL to insert stripes

selectRouteBlk -box 887.8500 1200.0000 1005.2800 1254.5000 defLayerBlkName -layer C1
deleteSelectedFromFPlan


addStripe -nets {VDD VSS} -layer C5 -direction vertical -width 0.34 -spacing 2 -set_to_set_distance 10 \
-area {888 1252.50 1005.3 1201.91} -start_from left -switch_layer_over_obs false -max_same_layer_jog_length 2 -padcore_ring_top_layer_limit LB \
-padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 -use_wire_group 0 -snap_wire_center_to_grid None \
-skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

addStripe -nets {VNW_N VPW_P} -layer C5 -direction vertical -width 0.17 -spacing 1 -set_to_set_distance 10 \
-area {892.68 1252.50 1005.3 1201.91} -start_from left -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 -use_wire_group 0 \
-snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

