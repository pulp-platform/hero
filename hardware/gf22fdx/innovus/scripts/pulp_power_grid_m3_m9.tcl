###########################################################################
#  power grid creation
###########################################################################

#REF: 22FDX_Rev1.1_2.0_20170410.pdf

#page 494, Cx.W.1
#even multiple of manufacturing grid (0.001000), setting to 0.046000.
set minC1_W 0.044
#page 493, Ax.S.1 for VIAs but for long lenght Cx.S.11 is used
set minC1_S 0.45
#page 494, Cx.W.1
set minC2_W 0.046
#page 493, Cx.S.11
set minC2_S 0.45

## let us start with a cleanup
deleteAllPowerPreroutes
clearDrc
setViaGenMode    -reset
setAddStripeMode -reset
setSrouteMode    -reset

setViaGenMode -optimize_cross_via true
setAddStripeMode -stacked_via_bottom_layer 2 -stacked_via_top_layer 3

#VBN VBP (M3)

#stop at 1200 and then restart from there as it was divergin from welltap PINS
addStripe -skip_via_on_pin {} \
          -set_to_set_distance 29.95 -spacing  0.32 -start_offset  30.164 -stop_offset 600 -width 0.046 \
          -same_layer_target_only 1 -max_same_layer_jog_length 4 \
          -padcore_ring_bottom_layer_limit 1 -padcore_ring_top_layer_limit 6 \
          -block_ring_bottom_layer_limit 1 -block_ring_top_layer_limit 6 \
          -layer C1 \
          -nets {VNW_N VPW_P}

addStripe -skip_via_on_pin {} \
          -set_to_set_distance 29.95 -spacing  0.32 -start_offset  1258.2 -width 0.046 \
          -same_layer_target_only 1 -max_same_layer_jog_length 4 \
          -padcore_ring_bottom_layer_limit 1 -padcore_ring_top_layer_limit 6 \
          -block_ring_bottom_layer_limit 1 -block_ring_top_layer_limit 6 \
          -layer C1 \
          -nets {VNW_N VPW_P}

setViaGenMode    -reset
setAddStripeMode -reset

setAddStripeMode -ignore_block_check false -break_at none -route_over_rows_only false \
                 -rows_without_stripes_only false -extend_to_closest_target none -stop_at_last_wire_for_area false \
                 -partial_set_thru_domain false -ignore_nondefault_domains false -trim_antenna_back_to_shape none \
                 -spacing_type edge_to_edge -spacing_from_block 0 -stripe_min_length 0 -stacked_via_top_layer LB \
                 -stacked_via_bottom_layer M2 -via_using_exact_crossover_size false -split_vias false -orthogonal_only true \
                 -allow_jog { padcore_ring  block_ring }
#VDD GND GND (M3)

addStripe -skip_via_on_pin {} \
          -set_to_set_distance 29.95 -spacing  0 -start_offset  0.986  -width 0.68 \
          -same_layer_target_only 1 -max_same_layer_jog_length 4 \
          -padcore_ring_bottom_layer_limit 1 -padcore_ring_top_layer_limit 6 \
          -block_ring_bottom_layer_limit 1 -block_ring_top_layer_limit 6 \
          -layer C1 \
          -nets {VDD}

addStripe -skip_via_on_pin {} \
          -set_to_set_distance 29.95 -spacing  0 -start_offset  7.906 -width 0.34 \
          -same_layer_target_only 1 -max_same_layer_jog_length 4 \
          -padcore_ring_bottom_layer_limit 1 -padcore_ring_top_layer_limit 6 \
          -block_ring_bottom_layer_limit 1 -block_ring_top_layer_limit 6 \
          -layer C1 \
          -nets {VSS}

addStripe -skip_via_on_pin {} \
          -set_to_set_distance 29.95 -spacing  0 -start_offset  11.056 -width 0.34 \
          -same_layer_target_only 1 -max_same_layer_jog_length 4 \
          -padcore_ring_bottom_layer_limit 1 -padcore_ring_top_layer_limit 6 \
          -block_ring_bottom_layer_limit 1 -block_ring_top_layer_limit 6 \
          -layer C1 \
          -nets {VSS}

#Wires removed because of minStep Violation on the ENDCAP at the left of the FLL
#and at the very end of the floorplan
#selectWire 640.0060 268.1160 640.3460 1264.9600 3 VSS
#selectWire 1328.8560 0.0000 1329.1960 1264.9600 3 VSS
#deleteSelectedFromFPlan

#addStripe -nets VDD -layer C3 -direction horizontal -width 0.34 -spacing 0 -set_to_set_distance 29.95 -start_from top -start 7.906 -stop 636 -switch_layer_over_obs false -max_same_layer_jog_length 2 -padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 -use_wire_group 0 -snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }


#big GRID, horizontal

addStripe -nets VDD -layer IA -direction horizontal -width 4.546 -extend_to design_boundary -create_pins 1 \
-spacing 0 -set_to_set_distance 50 -start_from top -start 1250.38 -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 \
-use_wire_group 0 -snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

addStripe -nets VNW_N -layer IA -direction horizontal -width 1.442 -extend_to design_boundary -create_pins 1 \
-spacing 0 -set_to_set_distance 50 -start_from top -start 1243.834 -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 \
-use_wire_group 0 -snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

addStripe -nets VPW_P -layer IA -direction horizontal -width 1.442 -extend_to design_boundary -create_pins 1 \
-spacing 0 -set_to_set_distance 50 -start_from top -start 1240.392 -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 \
-use_wire_group 0 -snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

addStripe -nets VSS -layer IA -direction horizontal -width 4.546 -extend_to design_boundary -create_pins 1 \
-spacing 0 -set_to_set_distance 50 -start_from top -start 1236.952 -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 \
-use_wire_group 0 -snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

addStripe -nets VDD_ARR -layer IA -direction horizontal -width 1.442 -extend_to design_boundary -create_pins 1 \
-spacing 0 -set_to_set_distance 50 -start_from top -start 1230.406 -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 \
-use_wire_group 0 -snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

addStripe -nets VDD_PER -layer IA -direction horizontal -width 1.442 -extend_to design_boundary -create_pins 1 \
-spacing 0 -set_to_set_distance 50 -start_from top -start 1226.964 -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 \
-use_wire_group 0 -snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

addStripe -nets VDD -layer IA -direction horizontal -width 4.546 -extend_to design_boundary -create_pins 1 \
-spacing 0 -set_to_set_distance 50 -start_from top -start 1223.522 -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 \
-use_wire_group 0 -snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

addStripe -nets VDD_ARR -layer IA -direction horizontal -width 1.442 -extend_to design_boundary -create_pins 1 \
-spacing 0 -set_to_set_distance 50 -start_from top -start 1216.976 -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 \
-use_wire_group 0 -snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

addStripe -nets VDD_PER -layer IA -direction horizontal -width 1.442 -extend_to design_boundary -create_pins 1 \
-spacing 0 -set_to_set_distance 50 -start_from top -start 1213.534 -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 \
-use_wire_group 0 -snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }


addStripe -nets VSS -layer IA -direction horizontal -width 4.546 -extend_to design_boundary -create_pins 1 \
-spacing 0 -set_to_set_distance 50 -start_from top -start 1210.092 -switch_layer_over_obs false -max_same_layer_jog_length 2 \
-padcore_ring_top_layer_limit LB -padcore_ring_bottom_layer_limit M1 -block_ring_top_layer_limit LB -block_ring_bottom_layer_limit M1 \
-use_wire_group 0 -snap_wire_center_to_grid None -skip_via_on_pin {  standardcell } -skip_via_on_wire_shape {  noshape }

deselectAll
