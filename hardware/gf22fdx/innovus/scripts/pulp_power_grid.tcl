###########################################################################
#  power grid creation
##########################################################################

setViaGenMode    -reset
setAddStripeMode -reset
setSrouteMode    -reset

#Resize VIAs

#VDD
  #M9->M8
editSelectVia -net VDD -cut_layer YX
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 1 -via_rows 2
  #M8->M7
editSelectVia -net VDD -cut_layer A5
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 6 -via_rows 9

  #M7->M6
editSelectVia -net VDD -cut_layer A4
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 6 -via_rows 9
  #M6->M5
editSelectVia -net VDD -cut_layer A3
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 6 -via_rows 9
  #M5->M4
editSelectVia -net VDD -cut_layer A2
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 6 -via_rows 9
  #M4->M3
editSelectVia -net VDD -cut_layer A1
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 6 -via_rows 9

#VSS
  #M9->M8
editSelectVia -net VSS -cut_layer YX
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 1 -via_rows 2
  #M8->M7
editSelectVia -net VSS -cut_layer A5
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 2 -via_rows 6
  #M7->M6
editSelectVia -net VSS -cut_layer A4
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 2 -via_rows 6
  #M6->M5
editSelectVia -net VSS -cut_layer A3
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 2 -via_rows 6
  #M5->M4
editSelectVia -net VSS -cut_layer A2
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 2 -via_rows 6
  #M4->M3
editSelectVia -net VSS -cut_layer A1
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 2 -via_rows 6


#VNW_N
  #M9->M8
editSelectVia -net VNW_N -cut_layer YX
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 1 -via_rows 2
  #M8->M7
editSelectVia -net VNW_N -cut_layer A5
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 1 -via_rows 6
  #M7->M6
editSelectVia -net VNW_N -cut_layer A4
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 1 -via_rows 6
  #M6->M5
editSelectVia -net VNW_N -cut_layer A3
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 1 -via_rows 6
  #M5->M4
editSelectVia -net VNW_N -cut_layer A2
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 1 -via_rows 6
  #M4->M3
editSelectVia -net VNW_N -cut_layer A1
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 1 -via_rows 6


#VPW_P
  #M9->M8
editSelectVia -net VPW_P -cut_layer YX
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 1 -via_rows 2
  #M8->M7
editSelectVia -net VPW_P -cut_layer A5
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 1 -via_rows 6
  #M7->M6
editSelectVia -net VPW_P -cut_layer A4
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 1 -via_rows 6
  #M6->M5
editSelectVia -net VPW_P -cut_layer A3
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 1 -via_rows 6
  #M5->M4
editSelectVia -net VPW_P -cut_layer A2
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 1 -via_rows 6
  #M4->M3
editSelectVia -net VPW_P -cut_layer A1
editPowerVia -modify_vias 1 -selected_vias 1 -via_columns 1 -via_rows 6


setAddStripeMode -ignore_block_check false -break_at none -route_over_rows_only false \
                 -rows_without_stripes_only false -extend_to_closest_target none -stop_at_last_wire_for_area false \
                 -partial_set_thru_domain false -ignore_nondefault_domains false -trim_antenna_back_to_shape none \
                 -spacing_type edge_to_edge -spacing_from_block 0 -stripe_min_length 0 -stacked_via_top_layer LB \
                 -stacked_via_bottom_layer M2 -via_using_exact_crossover_size false -split_vias false -orthogonal_only true \
                 -allow_jog { padcore_ring  block_ring }

source scripts/stripes_block_power_grid.tcl

#prevent VIA from M10 to M8-M3, just do via on M9
setAddStripeMode -stacked_via_bottom_layer 9 -stacked_via_top_layer 10


#big GRID, vertical

addStripe -nets VDD -layer IB -direction vertical -width 4.546 \
-spacing 0 -set_to_set_distance 50 -start_from top -start 1.9 -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 \
-use_wire_group 0 -snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

addStripe -nets VDD_ARR -layer IB -direction vertical -width 1.442 \
-spacing 0 -set_to_set_distance 50 -start_from top -start 8.446 -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 \
-use_wire_group 0 -snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

addStripe -nets VDD_PER -layer IB -direction vertical -width 1.442 \
-spacing 0 -set_to_set_distance 50 -start_from top -start 11.888 -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 \
-use_wire_group 0 -snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

addStripe -nets VSS -layer IB -direction vertical -width 4.546 \
-spacing 0 -set_to_set_distance 50 -start_from top -start 15.33 -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 \
-use_wire_group 0 -snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

addStripe -nets VDD_ARR -layer IB -direction vertical -width 1.442 \
-spacing 0 -set_to_set_distance 50 -start_from top -start 21.876 -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 \
-use_wire_group 0 -snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

addStripe -nets VDD_PER -layer IB -direction vertical -width 1.442 \
-spacing 0 -set_to_set_distance 50 -start_from top -start 25.318 -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 \
-use_wire_group 0 -snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

addStripe -nets VDD -layer IB -direction vertical -width 4.546 \
-spacing 0 -set_to_set_distance 50 -start_from top -start 28.76 -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 \
-use_wire_group 0 -snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

addStripe -nets VNW_N -layer IB -direction vertical -width 1.442 \
-spacing 0 -set_to_set_distance 50 -start_from top -start 35.306 -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 \
-use_wire_group 0 -snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

addStripe -nets VPW_P -layer IB -direction vertical -width 1.442 \
-spacing 0 -set_to_set_distance 50 -start_from top -start 38.748 -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 \
-use_wire_group 0 -snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

addStripe -nets VDD -layer IB -direction vertical -width 4.546 \
-spacing 0 -set_to_set_distance 50 -start_from top -start 42.19 -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 \
-use_wire_group 0 -snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }



#Unroutable margin
#set floorMargin_routBlk [expr $floorMargin - 0.05]
#createRouteBlk -box 0 0 $floorMargin_routBlk $floorH -layer {M1 M2 C1 C2 C3 C4 C5 C6}
#createRouteBlk -box [expr $floorW - $floorMargin_routBlk] 0 $floorW $floorH -layer {M1 M2 C1 C2 C3 C4 C5 C6}

#createRouteBlk -box 0 [expr $floorH - $floorMargin_routBlk] $floorW $floorH -layer {M1 M2 C1 C2 C3 C4 C5 C6}
#createRouteBlk -box 0 0 $floorW [expr $floorMargin_routBlk - 0.02] -layer {M1 M2 C1 C2 C3 C4 C5 C6}



#deselectAll
#selectRouteBlk -box 0.0000 0.0000 1319.9680 0.4300 defLayerBlkName -layer C6
#deleteSelectedFromFPlan
#selectRouteBlk -box 0.0000 0.0000 0.4500 1254.9600 defLayerBlkName -layer C6
#deleteSelectedFromFPlan
#selectRouteBlk -box 0.0000 1254.5500 1319.9680 1254.9600 defLayerBlkName -layer C6
#deleteSelectedFromFPlan
#selectRouteBlk -box 1319.5500 0.0000 1319.9680 1254.9600 defLayerBlkName -layer C6
#deleteSelectedFromFPlan
