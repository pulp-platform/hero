#SETUP
sh date
sh echo "Current git version is `git rev-parse --short HEAD`"
source scripts/rm_setup/design_setup.tcl

#SYNTHESIS SCRIPT
source scripts/utils/colors.tcl
source scripts/utils/print_logo.tcl
source scripts/utils/area_report.tcl

# ENVIRONMET SETUP
#Create Folders
#source scripts/utils/create_folder.tcl

suppress_message { VER-130 }
set_host_option -max_core $NUM_CORES

#When set to true, this variable enables advanced analysis through transparent latches during timing updates and reporting. When set to false (the default), this variable disables advanced analysis and reporting through transparent latches.
set timing_enable_through_paths true

# This valiable replaces -timing_high_effort_script option in compile ultra which is ignored.
set compile_timing_high_effort true

set reAnalyzeRTL "TRUE"

set DESIGN_NAME  "pulp"

# Set VERILOG defines
set DEFINES "SYNTHESIS=1"
set DEFINE "INVECAS=1"

sh mkdir -p unmapped

# ANALIZE THE RTL CODE or Read the GTECH
if { $reAnalyzeRTL == "TRUE" } {
    file delete -force -- ./work
    source -echo -verbose ./scripts/analyze_auto/ips_add_files.tcl
    source -echo -verbose ./scripts/analyze_auto/rtl_add_files.tcl
    elaborate pulp

    write -format verilog -hier -o ./unmapped/pulp_unmapped.v
    write -format ddc -hier -o ./unmapped/pulp_unmapped.ddc pulp
} else {
     read_file  -format ddc  ./unmapped/pulp_unmapped.ddc
}

current_design pulp
link
after 10000
set uniquify_naming_style "soc_%s_%d"
uniquify -force


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

#14)
exit
