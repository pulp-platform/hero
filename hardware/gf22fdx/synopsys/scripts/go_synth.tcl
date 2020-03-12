source scripts/go_elab.tcl
after 10000
set uniquify_naming_style "soc_%s_%d"
uniquify -force

#############
##   UPF   ##
#############

create_scenario SSG_0P72V_0P00V_${VBN}V_${VBP}V_RCmax_${TEMP}
current_scenario SSG_0P72V_0P00V_${VBN}V_${VBP}V_RCmax_${TEMP}
set_scenario_options -leakage_power true -dynamic_power true
set_operating_conditions SSG_0P72V_0P00V_${VBN}V_${VBP}V_${TEMP}

# Read RC estimation files
set_tlu_plus_files -max_tluplus  $tlu_path/10M_2Mx_6Cx_2Ix_LBthick/22fdsoi_10M_2Mx_6Cx_2Ix_LBthick_FuncRCmax_detailed.tluplus \
                   -tech2itf_map $tech_mw_path/10M_2Mx_6Cx_2Ix_LB/22FDSOI_10M_2Mx_6Cx_2Ix_LB_StarRCXT_MW.map
check_tlu_plus_files

report_timing -loop -max_paths 100 > TIMING_LOOP.rpt

# Ungroup script
source -echo -verbose scripts/ungroup_script.tcl
after 3000

source -echo -verbose  scripts/constraints/constraints_mode0.sdc
source -echo -verbose  scripts/create_path_groups.tcl

# INSERT CLOCK GATE
source -echo -verbose ./scripts/insert_clock_gating.tcl


# retiming
set_optimize_registers true -minimum_period_only -designs "*fpnew_*"

# critical range for debug only
set_critical_range 200 *

# Compile Ultra
compile_ultra -no_autoungroup -no_boundary_optimization -timing -gate_clock

# Reports
sh mkdir -p ./reports

report_timing -max_paths 100 -nosplit > reports/timing.rpt
report_area  -hier -nosplit > reports/area.rpt
report_resources   -hierarchy > reports/dp_resource.rpt

# Dump Verilog
sh mkdir -p ./mapped
write -f ddc -hierarchy  -output ./mapped/$OUT_FILENAME.ddc

change_names -rules verilog -hier
define_name_rules fixbackslashes -allowed "A-Za-z0-9_" -first_restricted "\\" -remove_chars
change_names -rule fixbackslashes -h

sh mkdir -p ./export
write -format verilog -hier -o ./export/$OUT_FILENAME.v

sh date
sh echo "Current git version is `git rev-parse --short HEAD`"

start_gui

#14)
#exit
