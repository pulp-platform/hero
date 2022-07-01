##=====================================================
## Using Verilator
##=====================================================
#DESIGN 			= pulp_cluster
#VCODE 			= vcode.f
#WORKLIB 		= worklib
#
#VERILATOR 		= verilator
#VERILATOR_FLAG 	= -sc --exe --build -j --assert -sv +1800-2017ext+sv +notimingchecks
#VERILATOR_FLAG += --trace +define+VM_TRACE=1
#VERILATOR_FLAG += +define+SYNTHESIS +define+TARGET_SYNTHESIS
#VERILATOR_FLAG += -Wall -Wno-BLKANDNBLK -Wno-LITENDIAN -Wno-CASEINCOMPLETE -Wno-CMPCONST -Wno-WIDTH -Wno-WIDTHCONCAT -Wno-UNSIGNED -Wno-UNOPTFLAT -Wno-fatal -Wno-UNUSED
#VERILATOR_FLAG += --Mdir ${WORKLIB}
#VERILATOR_FLAG += --top-module ${DESIGN}
#VERILATOR_INPUT = -f ${VCODE} ${DESIGN}.cpp
#
#.PHONY: default
#default:
#	${VERILATOR} ${VERILATOR_FLAG} ${VERILATOR_INPUT}
#	${WORKLIB}/V${DESIGN} +trace
#
#.PHONY: clean
#maintainer-copy::
#clean mostlyclean distclean maintainer-clean::
#	-rm -rf ${WORKLIB} *.log *dump *bpd core



#=====================================================
# Using Verilator
#=====================================================
DESIGN 			= sc_main
VCODE 			= vcode.f
WORKLIB 		= worklib

VLT_MODEL_PATH  = ${HERO_DIR}/hardware/verilator_model

VERILATOR 		= verilator
# Generate SystemC in executable form
VERILATOR_FLAGS =  -sc --exe --build --assert
#VERILATOR_FLAGS += -x-assign fast
VERILATOR_FLAGS += -sv +1800-2017ext+sv
VERILATOR_FLAGS += +notimingchecks
VERILATOR_FLAGS += --trace +define+VM_TRACE=1
VERILATOR_FLAGS += +define+SYNTHESIS +define+TARGET_SYNTHESIS
VERILATOR_FLAGS += -Wall -Wno-BLKANDNBLK -Wno-LITENDIAN -Wno-CASEINCOMPLETE \
				   -Wno-CMPCONST -Wno-WIDTH -Wno-WIDTHCONCAT -Wno-UNSIGNED \
				   -Wno-UNOPTFLAT -Wno-fatal -Wno-UNUSED
VERILATOR_FLAGS += -I${VLT_MODEL_PATH}
VERILATOR_FLAGS += --Mdir ${WORKLIB}
VERILATOR_FLAGS += --top-module pulp_cluster
VERILATOR_INPUT = -f ${VCODE} \
				  ${VLT_MODEL_PATH}/sc_main.cpp 

# Check if SC exists via a verilator call (empty if not)
SYSTEMC_EXISTS  = $(shell $(VERILATOR) --getenv SYSTEMC_INCLUDE)

.PHONY: default
default:
	${VERILATOR} ${VERILATOR_FLAGS} ${VERILATOR_INPUT}
	${WORKLIB}/V${DESIGN} +trace

.PHONY: clean
maintainer-copy::
clean mostlyclean distclean maintainer-clean::
	-rm -rf ${WORKLIB} *.log *dump *bpd core

#clear ; g++ ../verilator_model/sc_main.cpp worklib/Vpulp_cluster.cpp -I./worklib -I../verilator_model -I/opt/verilator_v4.222/share/verilator/include | & tee vlt.log
