# Copyright 2018 ETH Zurich and University of Bologna.                       #
# Copyright and related rights are licensed under the Solderpad Hardware     #
# License, Version 0.51 (the "License"); you may not use this file except in #
# compliance with the License.  You may obtain a copy of the License at      #
# http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law  #
# or agreed to in writing, software, hardware and materials distributed under#
# this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR     #
# CONDITIONS OF ANY KIND, either express or implied. See the License for the #
# specific language governing permissions and limitations under the License. #

set PULP_PATH="../../GAP"

vlog -sv -work work -quiet ../RTL/cache_controller_to_axi_128_PF.sv 
vlog -sv -work work -quiet ../RTL/central_controller_128.sv
vlog -sv -work work -quiet ../RTL/icache_bank_mp_128.sv +incdir+${PULP_PATH}/fe/rtl/includes
vlog -sv -work work -quiet ../RTL/icache_bank_mp_PF.sv  +incdir+${PULP_PATH}/fe/rtl/includes
vlog -sv -work work -quiet ../RTL/icache_top_mp_128_PF.sv +incdir+${PULP_PATH}/fe/rtl/includes
vlog -sv -work work -quiet ../RTL/merge_refill_cam_128_16.sv
vlog -sv -work work -quiet ../RTL/pf_miss_mux.sv
vlog -sv -work work -quiet ../RTL/prefetcher_if.sv

#INDIR is needed only to include ${PULP_PATH}/fe/rtl/includes/ulpsoc_defines.sv
# only this defien is used to enable/disable the perf Counters 
# `define FEATURE_ICACHE_STAT



#Dependancies!!!!
vlog -sv -work work -quiet ${PULP_PATH}/fe/ips/axi/axi_slice/axi_r_buffer.sv
vlog -sv -work work -quiet ${PULP_PATH}/fe/ips/axi/axi_slice/axi_ar_buffer.sv
vlog -sv -work work -quiet ${PULP_PATH}/fe/ips/axi/axi_slice/axi_buffer.sv

vlog -sv -work work -quiet ${PULP_PATH}/fe/ips/common_cells/generic_fifo.sv
vlog -sv -work work -quiet ${PULP_PATH}/fe/ips/common_cells/generic_LFSR_8bit.sv
vlog -sv -work work -quiet ${PULP_PATH}/fe/ips/common_cells/onehot_to_bin.sv
vlog -sv -work work -quiet ${PULP_PATH}/fe/ips/tech_cells_generic/cluster_clock_gating.sv

vlog -sv -work work -quiet ${PULP_PATH}/fe/ips/icache-intc/DistributedArbitrationNetwork_Req_icache_intc.sv
vlog -sv -work work -quiet ${PULP_PATH}/fe/ips/icache-intc/DistributedArbitrationNetwork_Resp_icache_intc.sv
vlog -sv -work work -quiet ${PULP_PATH}/fe/ips/icache-intc/icache_intc.sv
vlog -sv -work work -quiet ${PULP_PATH}/fe/ips/icache-intc/Req_Arb_Node_icache_intc.sv
vlog -sv -work work -quiet ${PULP_PATH}/fe/ips/icache-intc/Resp_Arb_Node_icache_intc.sv
vlog -sv -work work -quiet ${PULP_PATH}/fe/ips/icache-intc/RoutingBlock_Req_icache_intc.sv
vlog -sv -work work -quiet ${PULP_PATH}/fe/ips/icache-intc/RoutingBlock_Resp_icache_intc.sv

vlog -sv -work work -quiet ${PULP_PATH}/fe/ips/scm/latch_scm/register_file_1w_multi_port_read.sv 
vlog -sv -work work -quiet ${PULP_PATH}/fe/rtl/components/pulp_interfaces.sv +incdir+${PULP_PATH}/fe/rtl/includes
