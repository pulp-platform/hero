##########################################################################
#  Design Setings
##########################################################################

set_power_output_dir -reset
set_power_output_dir  power
set_default_switching_activity -reset
set_default_switching_activity -input_activity 0.0 -period 10.0
read_activity_file -reset
read_activity_file -format VCD -scope tb/i_dut/pulpissimo_i -start 5175018ns -end 5278601ns -block {} ../power_estimations/VCD/matmul.vcd
set_power -reset
set_powerup_analysis -reset
set_dynamic_power_simulation -reset
#report_power -view view_tt_025C_Nom -rail_analysis_format VS -outfile power/pulpissimo.rpt
report_power -rail_analysis_format VS -outfile power/pulpissimo.rpt


create_power_pads -net VDD     -auto_fetch -format padcell -vsrc_file save/VDD.pp
create_power_pads -net VDD_PER -auto_fetch -format padcell -vsrc_file save/VDD_PER.pp
create_power_pads -net VDD_ARR -auto_fetch -format padcell -vsrc_file save/VDD_ARR.pp
create_power_pads -net VSS     -auto_fetch -format padcell -vsrc_file save/VSS.pp

set_rail_analysis_mode -reset

set_rail_analysis_mode -method static -power_switch_eco false \
-accuracy hd -force_library_merging true -power_grid_library \
{   ../technology/cl/GF22FDX_SC8T_104CPP_BASE_CSC20L_TT_0P80V_0P00V_0P00V_0P00V_25C.cl \
    ../technology/cl/GF22FDX_SC8T_104CPP_BASE_CSC24L_TT_0P800V_0P00V_0P00V_0P00V_25C.cl \
    ../technology/cl/GF22FDX_SC8T_104CPP_BASE_CSC28L_TT_0P800V_0P00V_0P00V_0P00V_25C.cl \
    ../technology/cl/IN22FDX_S1D_NFRG_W02048B032M04C128_TT_0P800V_0P800V_0P000V_0P000V_025C.cl \
    ../technology/cl/IN22FDX_S1D_NFRG_W04096B032M04C128_TT_0P800V_0P800V_0P000V_0P000V_025C.cl \
    ../technology/cl/IN22FDX_ROMI_FRG_W02048B032M32C064_boot_code_TT_0P800V_0P800V_0P000V_0P000V_025C.cl } \
     -process_techgen_em_rules false -enable_rlrp_analysis false -extraction_tech_file ../technology/qrc/qrcTechFile_nominal \
     -vsrc_search_distance 50 -ignore_shorts false -enable_manufacturing_effects false \
     -temp_directory_name ./tmp -report_via_current_direction false


#set_rail_analysis_mode -analysis_view view_tt_025C_Nom

set_pg_nets -reset
set_pg_nets -net VDD_PER -voltage 0.8 -threshold 0.76
set_pg_nets -net VDD -voltage 0.8 -threshold 0.76
set_pg_nets -net VDD_ARR -voltage 0.8 -threshold 0.76
set_pg_nets -net VSS -voltage 0 -threshold 0.04
set_rail_analysis_domain -name PD_core -pwrnets { VDD_PER VDD VDD_ARR } -gndnets { VSS }
set_power_data -reset
set_power_data -format current -scale 1 {power/pulpissimo.rpt}
set_power_pads -reset
set_power_pads -net VDD_PER -format xy -file save/VDD_PER.pp
set_power_pads -net VDD_ARR -format xy -file save/VDD_ARR.pp
set_power_pads -net VDD     -format xy -file save/VDD.pp
set_power_pads -net VSS     -format xy -file save/VSS.pp

analyze_rail -type domain  -output ./rail/ PD_core