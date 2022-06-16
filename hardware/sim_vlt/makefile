#=====================================================
# Using Verilator
#=====================================================

DESIGN 			= pulp_cluster
VCODE 			= vcode.f
WORKLIB 		= worklib

VERILATOR 		= verilator
VERILATOR_FLAG 	= -sc --exe --build -j --assert -sv +1800-2017ext+sv +notimingchecks
VERILATOR_FLAG += --trace +define+VM_TRACE=1
VERILATOR_FLAG += +define+SYNTHESIS +define+TARGET_SYNTHESIS
VERILATOR_FLAG += -Wall -Wno-BLKANDNBLK -Wno-LITENDIAN -Wno-CASEINCOMPLETE -Wno-CMPCONST -Wno-WIDTH -Wno-WIDTHCONCAT -Wno-UNSIGNED -Wno-UNOPTFLAT -Wno-fatal -Wno-UNUSED
VERILATOR_FLAG += --Mdir ${WORKLIB}
VERILATOR_FLAG += --top-module ${DESIGN}
VERILATOR_INPUT = -f ${VCODE} ${DESIGN}.cpp

.PHONY: default
default:
	${VERILATOR} ${VERILATOR_FLAG} ${VERILATOR_INPUT}
	${WORKLIB}/V${DESIGN} +trace

.PHONY: clean
maintainer-copy::
clean mostlyclean distclean maintainer-clean::
	-rm -rf ${WORKLIB} *.log *dump *bpd core
