# NOTE:
# This default synthesis script requires a set of predefined parameters.
# It should be sourced only from a design definition file defining them!

# REQUIRED PARAMETERS:
# TNAME:    test name in aegis.json
# DESIGN:   top-level design name
# ANALYZE:  path to analyze script
# TCK:      Clock frequency (iff using default constraints)

# load utils and tech init script
source ../../scripts/util.tcl
source scripts/prepare_tech.tcl

# initialize default optional parameters (default constraints define CLKNAME, TI, TO)
set_if_undef CONSTR "scripts/constraints.tcl"
set_if_undef PARAMS ""
set_if_undef CORES 8
set_if_undef RPTDIR "reports/$TNAME"
set_if_undef BBABORT 1

# create report directory
sh mkdir -p ${RPTDIR}

# enable multicore synthesis
set_host_options -max_cores ${CORES}

# build memories, wrapper, and loader script
sh make -j ${CORES} -C ../mems all_${TNAME}
sh make scripts/${TNAME}.mems.tcl

# load memories
source scripts/${TNAME}.mems.tcl

# analyze
redirect -variable ana {source ${ANALYZE}; analyze -format sverilog ../mems/src/${TNAME}.tc_sram.sv}
echo $ana > ${RPTDIR}/analyze.rpt
on_error_occurred "Analyze" "$ana" "exit 187"

# elaborate
redirect -variable elab {elaborate ${DESIGN} -parameters ${PARAMS}}
echo $elab > ${RPTDIR}/elaborate.rpt
on_error_occurred "Elaborate" "$elab" "exit 177"

# check for missing black boxes
set missing_bb 0
redirect -variable desmis {report_design_mismatch}
echo $desmis > ${RPTDIR}/design_mismatch.rpt
on_error_occurred "Blackbox absence check" "$desmis" "upvar missing_bb mbb; set mbb 1" \
    "Number of (missing logical cells|inferred pin directions for blackbox) : "

# if blackboxes were missing: update memory file, start over
if $missing_bb {
    if {[info exists secondrun]} {
        if $BBABORT {
            puts_fail "Missing blackboxes after memory generation; synthesis will abort"
            exit 167
        } else {
            puts_warn "Missing blackboxes after memory generation; synthesis will continue"
        }
    } else {
        puts_log "Determining missing memory macros and restarting synthesis"
        sh echo ${desmis} | python3 scripts/getmems.py > ../mems/${TNAME}.mems.txt
        rad
        set secondrun 1
        source scripts/synth.tcl
    }
}

# constraints: forego default clock constraints with empty path
if {$CONSTR ne ""} {
    redirect -variable constr {source ${CONSTR}}
    echo $constr > ${RPTDIR}/constraints.rpt
    on_error_occurred "Constraints" "$constr" "exit 157"
}

# analyze datapath
analyze_datapath_extraction > ${RPTDIR}/datapath_extraction.rpt

# compile design
redirect -variable comp {compile_exploration -no_autoungroup}
echo $comp > ${RPTDIR}/compile.rpt
on_error_occurred "Compile" "$comp" "exit 147"

# uniquify
# uniquify

# report
analyze_datapath > ${RPTDIR}/datapath.rpt
report_resources -hierarchy -nosplit > ${RPTDIR}/resources.rpt
report_hierarchy -nosplit > ${RPTDIR}/hierarchy.rpt
report_timing > ${RPTDIR}/timing.rpt
report_area -hierarchy -nosplit > ${RPTDIR}/area.rpt
report_qor > ${RPTDIR}/qor.rpt

# prepare verilog dump
change_names -rules verilog -hierarchy
define_name_rules fixbackslashes -allowed "A-Za-z0-9_" -first_restricted "\\" -remove_chars
change_names -rule fixbackslashes -h

# extract netlist
write_file -hierarchy -format verilog -output out/${TNAME}_netlist.v

exit 0
