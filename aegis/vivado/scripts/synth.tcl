# NOTE:
# This default synthesis script requires a set of predefined parameters.
# It should be sourced only from a design definition file defining them!

# load utils and tech init script
source ../scripts/util.tcl

# initialize default optional parameters (default constraints define CLKNAME, TI, TO)
set_if_undef CONSTR "scripts/constraints.tcl"
set_if_undef PARAMS ""
set_if_undef CORES 8
set_if_undef RPTDIR "reports/$TNAME"
set_if_undef PART "xczu9eg-ffvb1156-2-e"
set_if_undef BOARD "xilinx.com:zcu102:part0:3.3"

# create report directory
exec mkdir -p ${RPTDIR}

# create project
create_project ${TNAME} -part ${PART} -in_memory -verbose

# configure project
set_property board_part ${BOARD} [current_project]
set_param general.maxThreads ${CORES}
set_property XPM_LIBRARIES XPM_MEMORY [current_project]
set search_path ""

# analyze
source ${ANALYZE} > ${RPTDIR}/analyze.rpt
source scripts/fpga_sources.tcl >> ${RPTDIR}/analyze.rpt
on_error_occurred "Analyze" "[exec cat ${RPTDIR}/analyze.rpt]" "exit 187" "ERROR"

# specify top
set_property top ${DESIGN} [current_fileset]
update_compile_order -fileset sources_1

# read constraints: forego default clock constraints with empty path
if {$CONSTR ne ""} {
    read_xdc -unmanaged -mode out_of_context ${CONSTR} > ${RPTDIR}/constraints.rpt
    on_error_occurred "Constraints" "[exec cat ${RPTDIR}/constraints.rpt]" "exit 157" "ERROR"
}

# synthesis
synth_design -verbose -mode out_of_context -flatten_hierarchy rebuilt -top ${DESIGN} -part ${PART} > ${RPTDIR}/synth.rpt
on_error_occurred "Synthesis" "[exec cat ${RPTDIR}/synth.rpt]" "exit 147" "ERROR"
set_property HD.PARTITION 1 [current_design]

# opt design
opt_design -verbose > ${RPTDIR}/opt.rpt

# place design
place_design -verbose > ${RPTDIR}/place.rpt

# opt design
phys_opt_design -verbose > ${RPTDIR}/phys_opt.rpt

# route design
route_design -verbose > ${RPTDIR}/route.rpt

# report
report_utilization -hierarchical -verbose -file ${RPTDIR}/utilization.rpt
report_timing_summary -delay_type min_max -report_unconstrained -check_timing_verbose -max_paths 50 -input_pins -routable_nets -file ${RPTDIR}/timing.rpt

exit 0
