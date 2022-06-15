#=====================================================
# Using vivado
#=====================================================

DESIGN 		= top
VCODE 		= vcode.vivado.f
WORK 		= worklib
TCL 		= tb_sim.tcl
DUMP 		= l1_dump
DUMP_VCD	= true
COMP_OPT 	= -d SYNTHESIS \
			  -d VERILATOR \
			  -d TARGET_SYNTHESIS 
ELAB_OPT 	= ${COMP_OPT} -dup_entity_as_module

.DEFAULT: default
default : comp elab

include ${COMMON_DIR}/VIVADO/common_makefile
