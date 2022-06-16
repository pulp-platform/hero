#=====================================================
# Using Verilator
#=====================================================

DESIGN 		= top
VCODE 		= vcode.f
WORK 		= worklib
TCL 		= tb_sim.tcl
DUMP 		= l1_dump
DUMP_VCD	= true
DEFINE		= +define+SYNTHESIS +define+TARGET_SYNTHESIS 
RUN_OPT 	= --assert --autoflush --sc +notimingchecks \
			   -Wall -Wno-BLKANDNBLK -Wno-LITENDIAN -Wno-CASEINCOMPLETE -Wno-CMPCONST -Wno-WIDTH -Wno-WIDTHCONCAT -Wno-UNSIGNED -Wno-UNOPTFLAT -Wno-fatal

.DEFAULT: default
default : run_vlt

run_vlt:
	@echo "verilator -sv +1800-2017ext+  --Mdir ${WORK}  ${DEFINE}  ${RUN_OPT}  -f ${VCODE}  --top-module top" > vrun.csh
	@chmod 774 vrun.csh
	@./vrun.csh |&tee vlt.log
