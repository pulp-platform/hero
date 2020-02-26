create_project pulp_txilzu9eg ./pulp_txilzu9eg -part xczu9eg-ffvb1156-2-e
set_property part xczu9eg-ffvb1156-2-e [current_project]

source ./define_sources.tcl
add_files -norecurse -fileset [current_fileset] ./pulp_txilzu9eg.v
source ./define_defines_includes.tcl
add_files -norecurse -fileset constrs_1 {./pulp_txilzu9eg_synth.xdc ./pulp_txilzu9eg_impl.xdc}
set_property used_in_implementation false [get_files ./pulp_txilzu9eg_synth.xdc]
set_property used_in_synthesis false [get_files ./pulp_txilzu9eg_impl.xdc]
set_property top pulp_txilzu9eg [current_fileset]

synth_design -rtl -name rtl_1

ipx::package_project -root_dir . -vendor ethz.ch -library user -taxonomy /UserIP \
  -set_current true

# Ports and Interfaces
## Clock
ipx::add_bus_interface clk [ipx::current_core]
set clk [ipx::get_bus_interfaces clk -of_objects [ipx::current_core]]
set_property abstraction_type_vlnv xilinx.com:signal:clock_rtl:1.0 $clk
set_property bus_type_vlnv xilinx.com:signal:clock:1.0 $clk
set_property interface_mode slave $clk
ipx::add_bus_parameter FREQ_HZ $clk
ipx::add_port_map CLK $clk
set_property physical_name clk_i [ipx::get_port_maps CLK -of_objects $clk]
## Reset
ipx::add_bus_interface rst_n [ipx::current_core]
set rst [ipx::get_bus_interfaces rst_n -of_objects [ipx::current_core]]
set_property abstraction_type_vlnv xilinx.com:signal:reset_rtl:1.0 $rst
set_property bus_type_vlnv xilinx.com:signal:reset:1.0 $rst
ipx::add_port_map RST $rst
set_property physical_name rst_ni [ipx::get_port_maps RST -of_objects $rst]
## AXI Master
ipx::add_bus_interface mst [ipx::current_core]
set mst [ipx::get_bus_interfaces mst -of_objects [ipx::current_core]]
set_property abstraction_type_vlnv xilinx.com:interface:aximm_rtl:1.0 $mst
set_property bus_type_vlnv xilinx.com:interface:aximm:1.0 $mst
set_property interface_mode master $mst
ipx::add_bus_parameter NUM_READ_OUTSTANDING $mst
ipx::add_bus_parameter NUM_WRITE_OUTSTANDING $mst
set portmap {
  {AWID mst_aw_id_o}
  {AWADDR mst_aw_addr_o}
  {AWLEN mst_aw_len_o}
  {AWSIZE mst_aw_size_o}
  {AWBURST mst_aw_burst_o}
  {AWLOCK mst_aw_lock_o}
  {AWCACHE mst_aw_cache_o}
  {AWPROT mst_aw_prot_o}
  {AWQOS mst_aw_qos_o}
  {AWUSER mst_aw_user_o}
  {AWVALID mst_aw_valid_o}
  {AWREADY mst_aw_ready_i}
  {WDATA mst_w_data_o}
  {WSTRB mst_w_strb_o}
  {WLAST mst_w_last_o}
  {WVALID mst_w_valid_o}
  {WREADY mst_w_ready_i}
  {BID mst_b_id_i}
  {BRESP mst_b_resp_i}
  {BVALID mst_b_valid_i}
  {BREADY mst_b_ready_o}
  {ARID mst_ar_id_o}
  {ARADDR mst_ar_addr_o}
  {ARLEN mst_ar_len_o}
  {ARSIZE mst_ar_size_o}
  {ARBURST mst_ar_burst_o}
  {ARLOCK mst_ar_lock_o}
  {ARCACHE mst_ar_cache_o}
  {ARPROT mst_ar_prot_o}
  {ARQOS mst_ar_qos_o}
  {ARUSER mst_ar_user_o}
  {ARVALID mst_ar_valid_o}
  {ARREADY mst_ar_ready_i}
  {RID mst_r_id_i}
  {RDATA mst_r_data_i}
  {RRESP mst_r_resp_i}
  {RLAST mst_r_last_i}
  {RVALID mst_r_valid_i}
  {RREADY mst_r_ready_o}
}
foreach pair $portmap {
  set theirs [lindex $pair 0]
  set ours [lindex $pair 1]
  ipx::add_port_map $theirs $mst
  set_property physical_name $ours [ipx::get_port_maps $theirs -of_objects $mst]
}
ipx::associate_bus_interfaces -busif mst -clock clk [ipx::current_core]
## AXI Slave
ipx::add_bus_interface slv [ipx::current_core]
set slv [ipx::get_bus_interfaces slv -of_objects [ipx::current_core]]
set_property abstraction_type_vlnv xilinx.com:interface:aximm_rtl:1.0 $slv
set_property bus_type_vlnv xilinx.com:interface:aximm:1.0 $slv
set_property interface_mode slave $slv
ipx::add_bus_parameter NUM_READ_OUTSTANDING $slv
ipx::add_bus_parameter NUM_WRITE_OUTSTANDING $slv
set portmap {
  {AWID slv_aw_id_i}
  {AWADDR slv_aw_addr_i}
  {AWLEN slv_aw_len_i}
  {AWSIZE slv_aw_size_i}
  {AWBURST slv_aw_burst_i}
  {AWLOCK slv_aw_lock_i}
  {AWCACHE slv_aw_cache_i}
  {AWPROT slv_aw_prot_i}
  {AWQOS slv_aw_qos_i}
  {AWUSER slv_aw_user_i}
  {AWVALID slv_aw_valid_i}
  {AWREADY slv_aw_ready_o}
  {WDATA slv_w_data_i}
  {WSTRB slv_w_strb_i}
  {WLAST slv_w_last_i}
  {WVALID slv_w_valid_i}
  {WREADY slv_w_ready_o}
  {BID slv_b_id_o}
  {BRESP slv_b_resp_o}
  {BVALID slv_b_valid_o}
  {BREADY slv_b_ready_i}
  {ARID slv_ar_id_i}
  {ARADDR slv_ar_addr_i}
  {ARLEN slv_ar_len_i}
  {ARSIZE slv_ar_size_i}
  {ARBURST slv_ar_burst_i}
  {ARLOCK slv_ar_lock_i}
  {ARCACHE slv_ar_cache_i}
  {ARPROT slv_ar_prot_i}
  {ARQOS slv_ar_qos_i}
  {ARUSER slv_ar_user_i}
  {ARVALID slv_ar_valid_i}
  {ARREADY slv_ar_ready_o}
  {RID slv_r_id_o}
  {RDATA slv_r_data_o}
  {RRESP slv_r_resp_o}
  {RLAST slv_r_last_o}
  {RVALID slv_r_valid_o}
  {RREADY slv_r_ready_i}
}
foreach pair $portmap {
  set theirs [lindex $pair 0]
  set ours [lindex $pair 1]
  ipx::add_port_map $theirs $slv
  set_property physical_name $ours [ipx::get_port_maps $theirs -of_objects $slv]
}
ipx::associate_bus_interfaces -busif slv -clock clk [ipx::current_core]
## AXI Lite RAB Conf Slave
ipx::add_bus_interface rab_conf [ipx::current_core]
set rab_conf [ipx::get_bus_interfaces rab_conf -of_objects [ipx::current_core]]
set_property abstraction_type_vlnv xilinx.com:interface:aximm_rtl:1.0 $rab_conf
set_property bus_type_vlnv xilinx.com:interface:aximm:1.0 $rab_conf
set_property interface_mode slave $rab_conf
ipx::add_bus_parameter NUM_READ_OUTSTANDING $rab_conf
ipx::add_bus_parameter NUM_WRITE_OUTSTANDING $rab_conf
set portmap {
  {AWADDR rab_conf_aw_addr_i}
  {AWPROT rab_conf_aw_prot_i}
  {AWVALID rab_conf_aw_valid_i}
  {AWREADY rab_conf_aw_ready_o}
  {WDATA rab_conf_w_data_i}
  {WSTRB rab_conf_w_strb_i}
  {WVALID rab_conf_w_valid_i}
  {WREADY rab_conf_w_ready_o}
  {BRESP rab_conf_b_resp_o}
  {BVALID rab_conf_b_valid_o}
  {BREADY rab_conf_b_ready_i}
  {ARADDR rab_conf_ar_addr_i}
  {ARPROT rab_conf_ar_prot_i}
  {ARVALID rab_conf_ar_valid_i}
  {ARREADY rab_conf_ar_ready_o}
  {RDATA rab_conf_r_data_o}
  {RRESP rab_conf_r_resp_o}
  {RVALID rab_conf_r_valid_o}
  {RREADY rab_conf_r_ready_i}
}
foreach pair $portmap {
  set theirs [lindex $pair 0]
  set ours [lindex $pair 1]
  ipx::add_port_map $theirs $rab_conf
  set_property physical_name $ours [ipx::get_port_maps $theirs -of_objects $rab_conf]
}
ipx::associate_bus_interfaces -busif rab_conf -clock clk [ipx::current_core]

# Address Space
ipx::add_address_space Data [ipx::current_core]
set_property master_address_space_ref Data \
  [ipx::get_bus_interfaces mst -of_objects [ipx::current_core] \
]
set_property width 64 [ipx::get_address_spaces Data -of_objects [ipx::current_core]]
set_property range_format string [ipx::get_address_spaces Data -of_objects [ipx::current_core]]
set_property range 16E [ipx::get_address_spaces Data -of_objects [ipx::current_core]]

set_property core_revision 4 [ipx::current_core]
ipx::update_source_project_archive -component [ipx::current_core]
ipx::create_xgui_files [ipx::current_core]
ipx::update_checksums [ipx::current_core]
ipx::save_core [ipx::current_core]
close_project
