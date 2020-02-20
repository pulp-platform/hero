##########################################################################
#  Design Setings
##########################################################################
set CHIP        "pulp_soc"
set DESIGNNAME  ${CHIP}
set reportDir  reports
set savePrefix ${DESIGNNAME}

setMultiCpuUsage -localCpu max
source scripts/custom_report.tcl

setLibraryUnit -time 1ps
setLibraryUnit -cap  1pf
##########################################################################
# load Config & FP
##########################################################################
source  ./src/pulp_soc.globals
init_design

report_analysis_views > reports/mmmc_view.rpt
set timing_report_group_based_mode true

setNanoRouteMode -reset
setNanoRouteMode -routeBottomRoutingLayer 2
setNanoRouteMode -routeTopRoutingLayer    8

set floorW [ expr 1840.0 ]
set floorH [ expr 1255.0 ]
set floorMargin 0.5
floorPlan -coreMarginsBy io -d  $floorW $floorH $floorMargin $floorMargin $floorMargin $floorMargin
source scripts/add_pin.tcl

##########################################################################
#  Memory and FLL Placements
##########################################################################
source scripts/pulp_soc_place_hm.tcl

##########################################################################
#  Settings: WellTaps and TIE cells
##########################################################################

source scripts/special_cell_setting.tcl
set wellTap(name) "SC8T_TAPX8_CSC20L"
set_well_tap_mode -reset
set_well_tap_mode -cell $wellTap(name) -rule $wellTap(maxdis)
#WELL TAP
addEndCap
addWellTap -cellInterval  $wellTap(maxdis) -fixedGap

#deleteFiller -prefix WELLTAP
#deleteFiller -prefix ENDCAP
##########################################################################
#  power Route
##########################################################################
free_power_intent
read_power_intent -cpf src/pulp_soc.cpf
commit_power_intent
fit

source scripts/pulp_soc_power_grid_m3_m9.tcl
source scripts/pulp_soc_power_viaResize_m3_m9_VDD.tcl
source scripts/pulp_soc_power_viaResize_m3_m9_VSS.tcl
source scripts/pulp_soc_power_stripes_blocks_m7.tcl
source scripts/pulp_soc_power_grid_m9_m10.tcl

# FOLLOW PINS
sroute -connect { corePin } \
       -allowLayerChange 1 \
       -corePinLayer M1 \
       -targetViaLayerRange [list M1 C1] \
       -layerChangeRange {M1 C1} \
       -allowJogging 0 \
       -targetPenetration { stripe 0 } \
       -nets "VDD VSS"
redraw

saveDesign save/pulp_top_01_floorplan.enc

write_lef_abstract save/pulp_soc.lef -stripePin

##########################################################################
# Placement
##########################################################################
echo "================================================================================"
echo "= Placement                                                                    ="
echo "================================================================================"

attachIOBuffer -in SC8T_INVX20_CSC28L -out SC8T_INVX20_CSC28L -suffix IOBUF -prePlace

setPlaceMode -place_global_cong_effort high \
             -place_global_timing_effort medium \
             -place_global_clock_gate_aware true \
             -place_global_ignore_scan true \
             -place_global_reorder_scan false \
             -place_global_place_io_pins false \
             -place_detail_color_aware_legal true \
             -place_detail_no_filler_without_implant true

setAnalysisMode -analysisType onChipVariation -cppr both

setAnalysisMode -aocv true

source scripts/pulp_soc_update_mmmc_sdc_prects.tcl

report_clocks                    >  reports/clocks_prePlace.rpt
report_clocks -uncertainty_table >> reports/clocks_prePlace.rpt

place_opt_design -out_dir reports/pulp_soc_02_place_opt_design
checkPlace
addTieHiLo
saveDesign save/pulp_top_02_placed.enc

timeDesign -preCTS -expandedViews -outDir reports/pulp_soc_02_timedesign_preCTS

##########################################################################
# CTS
##########################################################################
echo "================================================================================"
echo "= CTS                                                                          ="
echo "================================================================================"

#You have to generete this only the first time, then modify it according to your needs
#the modified file is scripts/pulp_soc.ccopt.tcl
#create_ccopt_clock_tree_spec -file src/create_ccopt_clock_tree_spec.innovus.spec.tcl
create_ccopt_clock_tree_spec -file src/pulp_soc.ccopt.tcl
source src/pulp_soc.ccopt.pre.tcl
source src/pulp_soc.ccopt.tcl
source src/pulp_soc.ccopt.post.tcl

ccopt_design -outDir reports/pulp_soc_03_ccopt_design

saveDesign save/pulp_top_03_cts.enc

source scripts/pulp_soc_update_mmmc_sdc_postcts.tcl

mkdir -p ./reports/clock

# report clock treee
report_ccopt_clock_trees -file ./reports/clock/clock_trees.rpt
report_ccopt_skew_groups -file ./reports/clock/skew_groups.rpt

timeDesign       -postCTS -expandedViews -outDir reports/pulp_soc_03_timedesign_postCTS
timeDesign -hold -postCTS -expandedViews -outDir reports/pulp_soc_03_timedesign_postCTS

optDesign -postCTS -hold

saveDesign save/pulp_top_03_cts_hold.enc

timeDesign       -postCTS -expandedViews -outDir reports/pulp_soc_03_timedesign_postCTS_hold
timeDesign -hold -postCTS -expandedViews -outDir reports/pulp_soc_03_timedesign_postCTS_hold

report_clocks                    >  reports/clocks_postCTS.rpt
report_clocks -uncertainty_table >> reports/clocks_postCTS.rpt

##########################################################################
# route
##########################################################################
echo "================================================================================"
echo "= Routing                                                                      ="
echo "================================================================================"

setNanoRouteMode -quiet -routeInsertAntennaDiode true
setNanoRouteMode -quiet -routeWithSiPostRouteFix false
setNanoRouteMode -quiet -routeWithTimingDriven   true
setNanoRouteMode -quiet -routeWithSiDriven       true
#setNanoRouteMode -quiet -drouteOnGridOnly true
## Prevent router modifying M1 pins shapes
setNanoRouteMode -routeWithViaInPin "1:1"
setNanoRouteMode -routeWithViaOnlyForStandardCellPin "1:1"
## limit VIAs to ongrid only for VIA01 (V1)
setNanoRouteMode -drouteOnGridOnly "via 1:1 wire 1:2"

routeDesign -globalDetail

saveDesign save/pulp_top_04_routed.enc

source scripts/pulp_soc_update_mmmc_sdc_postroute.tcl

timeDesign       -postRoute -expandedViews -outDir reports/pulp_soc_04_timedesign_postRoute
timeDesign -hold -postRoute -expandedViews -outDir reports/pulp_soc_04_timedesign_postRoute

report_clocks                    >  reports/clocks_postRoute.rpt
report_clocks -uncertainty_table >> reports/clocks_postRoute.rpt

setExtractRCMode -engine postRoute
setDelayCalMode -siAware true
#setOptMode -fixDrc true

source scripts/pulp_soc_update_mmmc_sdc_postroute_allViews_typ.tcl

optDesign -postRoute -hold

saveDesign save/pulp_top_04_routed_hold.enc

## setup and hold*** optDesign -postCTS
timeDesign       -postRoute -expandedViews -outDir reports/pulp_soc_04_timedesign_postRoute_hold
timeDesign -hold -postRoute -expandedViews -outDir reports/pulp_soc_04_timedesign_postRoute_hold

##########################################################################
# chip finishing
##########################################################################
echo "================================================================================"
echo "= Chip finishing                                                               ="
echo "================================================================================"

#search and repair loop to fix remaining drc violations
setNanoRouteMode -routeWithECO true
setNanoRouteMode -drouteFixAntenna true
globalDetailRoute
saveDesign save/pulp_top_preFiller.enc

#Remove the Fence, otherwise you get problem with filler cells
unplaceGuide soc_domain_i/ulpsoc_i/DC_SLICE_dc_fifo_dataout_bus_i

setFillerMode -doDRC true
setFillerMode -ecoMode true
addFiller

verify_drc
ecoRoute -fix_drc

saveDesign save/pulp_top_addFiller.enc

setNanoRouteMode -droutePostRouteSwapVia multiCut
routeDesign -viaOpt

#do final timing analysis
timedesign -postRoute -expandedViews       -outDir reports/timing -prefix pulp_soc_final
timedesign -postRoute -expandedViews -hold -outDir reports/timing -prefix pulp_soc_final

deleteRouteBlk -all
verify_drc -report reports/verify/pulp_soc.drc.rpt
verifyProcessAntenna -leffile reports/verify/pulp_soc.antenna.lef -reportfile reports/verify/pulp_soc.antenna.rpt
verifyWellTap -report  reports/verify/pulp_soc.wellTap.rpt

deleteEmptyModule

saveDesign save/pulp_top_final.enc

source scripts/pulp_soc_exportall.tcl

source scripts/checkdesign.tcl

set ff    [all_registers]
set mems  [all_registers -macros ]
set icgs  [filter_collection [all_registers] "is_integrated_clock_gating_cell == true"]
set regs  [remove_from_collection [all_registers -edge_triggered] $icgs]

#Create Mem Path Groups
group_path   -name Reg2Mem      -from $regs -to $mems
group_path   -name Mem2Reg      -from $mems -to $regs
group_path   -name Mem2Mem      -from $mems -to $mems

#Create FF Path Groups
group_path   -name ff2ff        -from $ff -to $ff
group_path   -name reg2ff       -from $regs -to $ff
group_path   -name ff2reg       -from $ff -to $regs


timedesign -postRoute -expandedViews       -outDir reports/timing -prefix pulp_soc_final_pathGroup
timedesign -postRoute -expandedViews -hold -outDir reports/timing -prefix pulp_soc_final_pathGroup

