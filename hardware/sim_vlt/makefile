#=====================================================
# Using Verilator
#=====================================================
DESIGN 			= pulp_cluster
VCODE 			= vcode.f
WORKLIB 		= worklib

VLT_MODEL_PATH  = ${HERO_DIR}/hardware/verilator_model

VERILATOR 		= verilator
# Generate SystemC in executable form
VERILATOR_FLAGS =  -cc --exe --build --assert -j
#VERILATOR_FLAGS += -x-assign fast
VERILATOR_FLAGS += -sv +1800-2017ext+sv
VERILATOR_FLAGS += +notimingchecks
VERILATOR_FLAGS += --trace -DVM_TRACE=1 -DVERILATOR_HAS_TRACE
VERILATOR_FLAGS += +define+SYNTHESIS +define+TARGET_SYNTHESIS
VERILATOR_FLAGS += -Wall -Wno-BLKANDNBLK -Wno-LITENDIAN -Wno-CASEINCOMPLETE \
				   -Wno-CMPCONST -Wno-WIDTH -Wno-WIDTHCONCAT -Wno-UNSIGNED \
				   -Wno-UNOPTFLAT -Wno-fatal -Wno-UNUSED
VERILATOR_FLAGS += -I${VLT_MODEL_PATH}
VERILATOR_FLAGS += --Mdir ${WORKLIB}
VERILATOR_FLAGS += --top-module ${DESIGN}
VERILATOR_INPUT = -f ${VCODE} \
				  ${VLT_MODEL_PATH}/main.cpp 

# # Check if SC exists via a verilator call (empty if not)
# SYSTEMC_EXISTS  = $(shell $(VERILATOR) --getenv SYSTEMC_INCLUDE)


.PHONY: default
default:
	@clear 
	@make clean 
	@make run |&tee vlt.log


.PHONY: run
run:
	${VERILATOR} ${VERILATOR_FLAGS} ${VERILATOR_INPUT}
	${WORKLIB}/V${DESIGN} +trace


.PHONY: clean
maintainer-copy::
clean mostlyclean distclean maintainer-clean::
	-rm -rf ${WORKLIB} *.log *dump *bpd core


.PHONY: rerun
rerun:
	@clear 
	@g++ ../verilator_model/main.cpp worklib/Vpulp_cluster.cpp -I./worklib -I../verilator_model -I/opt/tools/pulp/share/verilator/include |&tee vlt.log
