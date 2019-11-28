create_project hero_zcu102 ./hero_zcu102 -part xczu9eg-ffvb1156-2-e
set_property board_part xilinx.com:zcu102:part0:3.3 [current_project]
set_property ip_repo_paths ./vivado_ips [current_project]
update_ip_catalog

create_bd_design "hero_zcu102"
update_compile_order -fileset sources_1

# Zynq UltraScale+ Processor System
create_bd_cell -type ip -vlnv xilinx.com:ip:zynq_ultra_ps_e:3.3 i_zynq_ps
apply_bd_automation -rule xilinx.com:bd_rule:zynq_ultra_ps_e -config {apply_board_preset "1" } \
  [get_bd_cells i_zynq_ps]
set_property -dict [list \
  CONFIG.PSU__USE__M_AXI_GP1 {0} \
  CONFIG.PSU__USE__S_AXI_GP2 {1} \
  CONFIG.PSU__USE__IRQ1 {1} \
  CONFIG.PSU__CRL_APB__PL0_REF_CTRL__FREQMHZ {75} \
] [get_bd_cells i_zynq_ps]
connect_bd_net [get_bd_pins i_zynq_ps/pl_clk0] \
  [get_bd_pins i_zynq_ps/saxihp0_fpd_aclk]
connect_bd_net [get_bd_pins i_zynq_ps/pl_clk0] \
  [get_bd_pins i_zynq_ps/maxihpm0_fpd_aclk]

# System Reset
create_bd_cell -type ip -vlnv xilinx.com:ip:proc_sys_reset:5.0 i_sys_reset
connect_bd_net [get_bd_pins i_zynq_ps/pl_resetn0] \
  [get_bd_pins i_sys_reset/ext_reset_in]
connect_bd_net [get_bd_pins i_zynq_ps/pl_clk0] \
  [get_bd_pins i_sys_reset/slowest_sync_clk]

# Interconnect from Zynq PS
create_bd_cell -type ip -vlnv xilinx.com:ip:axi_interconnect:2.1 i_iconn_ps
set_property -dict [list CONFIG.NUM_MI {3}] [get_bd_cells i_iconn_ps]
connect_bd_net [get_bd_pins i_iconn_ps/ACLK] \
  [get_bd_pins i_zynq_ps/pl_clk0]
connect_bd_net [get_bd_pins i_iconn_ps/ARESETN] \
  [get_bd_pins i_sys_reset/peripheral_aresetn]
connect_bd_intf_net -boundary_type upper [get_bd_intf_pins i_iconn_ps/S00_AXI] \
  [get_bd_intf_pins i_zynq_ps/M_AXI_HPM0_FPD]
connect_bd_net [get_bd_pins i_iconn_ps/S00_ACLK] [get_bd_pins i_zynq_ps/pl_clk0]
connect_bd_net [get_bd_pins i_iconn_ps/S00_ARESETN] \
  [get_bd_pins i_sys_reset/peripheral_aresetn]
for {set i 0} {$i < 3} {incr i} {
  set clk [format "M%02d_ACLK" $i]
  set rst [format "M%02d_ARESETN" $i]
  connect_bd_net [get_bd_pins i_iconn_ps/$clk] [get_bd_pins i_zynq_ps/pl_clk0]
  connect_bd_net [get_bd_pins i_iconn_ps/$rst] [get_bd_pins i_sys_reset/peripheral_aresetn]
}

# Protocol Converter for RAB Config Port
create_bd_cell -type ip -vlnv xilinx.com:ip:axi_protocol_converter:2.1 i_prot_conv_rab_conf
set_property -dict [list CONFIG.SI_PROTOCOL.VALUE_SRC USER CONFIG.MI_PROTOCOL.VALUE_SRC USER] \
  [get_bd_cells i_prot_conv_rab_conf]
connect_bd_net [get_bd_pins i_prot_conv_rab_conf/aresetn] \
  [get_bd_pins i_sys_reset/peripheral_aresetn]
connect_bd_net [get_bd_pins i_prot_conv_rab_conf/aclk] [get_bd_pins i_zynq_ps/pl_clk0]
connect_bd_intf_net [get_bd_intf_pins i_prot_conv_rab_conf/S_AXI] -boundary_type upper \
  [get_bd_intf_pins i_iconn_ps/M01_AXI]

# GPIO to Control PULP
create_bd_cell -type ip -vlnv xilinx.com:ip:axi_gpio:2.0 i_gpio
set_property -dict [list CONFIG.C_GPIO_WIDTH {1} CONFIG.C_ALL_OUTPUTS {1}] [get_bd_cells i_gpio]
connect_bd_net [get_bd_pins i_gpio/s_axi_aclk] [get_bd_pins i_zynq_ps/pl_clk0]
connect_bd_net [get_bd_pins i_gpio/s_axi_aresetn] [get_bd_pins i_sys_reset/peripheral_aresetn]
connect_bd_intf_net [get_bd_intf_pins i_gpio/S_AXI] -boundary_type upper \
  [get_bd_intf_pins i_iconn_ps/M02_AXI]

# Concat for the PULP->Host IRQs
create_bd_cell -type ip -vlnv xilinx.com:ip:xlconcat:2.1 i_irq0_concat
set_property -dict [list CONFIG.NUM_PORTS {7}] [get_bd_cells i_irq0_concat]
connect_bd_net [get_bd_pins i_irq0_concat/dout] [get_bd_pins i_zynq_ps/pl_ps_irq0]
create_bd_cell -type ip -vlnv xilinx.com:ip:xlconcat:2.1 i_irq1_concat
set_property -dict [list CONFIG.NUM_PORTS {2}] [get_bd_cells i_irq1_concat]
connect_bd_net [get_bd_pins i_irq1_concat/dout] [get_bd_pins i_zynq_ps/pl_ps_irq1]

# PULP
create_bd_cell -type ip -vlnv ethz.ch:user:pulp_zcu102:1.0 i_pulp
connect_bd_net [get_bd_pins i_pulp/clk_i] [get_bd_pins i_zynq_ps/pl_clk0]
connect_bd_net [get_bd_pins i_pulp/rst_ni] [get_bd_pins i_sys_reset/peripheral_aresetn]
connect_bd_intf_net [get_bd_intf_pins i_pulp/mst] [get_bd_intf_pins i_zynq_ps/S_AXI_HP0_FPD]
connect_bd_intf_net -boundary_type upper [get_bd_intf_pins i_iconn_ps/M00_AXI] \
  [get_bd_intf_pins i_pulp/slv]
connect_bd_intf_net [get_bd_intf_pins i_prot_conv_rab_conf/M_AXI] \
  [get_bd_intf_pins i_pulp/rab_conf]
connect_bd_net [get_bd_pins i_gpio/gpio_io_o] [get_bd_pins i_pulp/cl_fetch_en_i]
connect_bd_net [get_bd_pins i_pulp/rab_miss_fifo_full_irq_o] [get_bd_pins i_irq0_concat/In0]
connect_bd_net [get_bd_pins i_pulp/rab_from_host_miss_irq_o] [get_bd_pins i_irq0_concat/In1]
connect_bd_net [get_bd_pins i_pulp/rab_from_host_multi_irq_o] [get_bd_pins i_irq0_concat/In2]
connect_bd_net [get_bd_pins i_pulp/rab_from_host_prot_irq_o] [get_bd_pins i_irq0_concat/In3]
connect_bd_net [get_bd_pins i_pulp/rab_from_pulp_miss_irq_o] [get_bd_pins i_irq0_concat/In4]
connect_bd_net [get_bd_pins i_pulp/rab_from_pulp_multi_irq_o] [get_bd_pins i_irq0_concat/In5]
connect_bd_net [get_bd_pins i_pulp/rab_from_pulp_prot_irq_o] [get_bd_pins i_irq0_concat/In6]
connect_bd_net [get_bd_pins i_pulp/cl_busy_o] [get_bd_pins i_irq1_concat/In0]
connect_bd_net [get_bd_pins i_pulp/cl_eoc_o] [get_bd_pins i_irq1_concat/In1]

# Address Map
assign_bd_address [get_bd_addr_segs {i_pulp/slv/Reg }]
set_property offset 0x00A0000000 [get_bd_addr_segs {i_zynq_ps/Data/SEG_i_pulp_Reg}]
set_property range 128M [get_bd_addr_segs {i_zynq_ps/Data/SEG_i_pulp_Reg}]
assign_bd_address [get_bd_addr_segs {i_pulp/rab_conf/Reg }]
set_property offset 0x00A8000000 [get_bd_addr_segs {i_zynq_ps/Data/SEG_i_pulp_Reg}]
set_property range 1M [get_bd_addr_segs {i_zynq_ps/Data/SEG_i_pulp_Reg1}]
assign_bd_address [get_bd_addr_segs {i_gpio/S_AXI/Reg }]
set_property offset 0x00A9000000 [get_bd_addr_segs {i_zynq_ps/Data/SEG_i_gpio_Reg}]
set_property range 4K [get_bd_addr_segs {i_zynq_ps/Data/SEG_i_gpio_Reg}]

# Validate and save Top-Level Block Design
save_bd_design
validate_bd_design
make_wrapper -files [get_files \
  ./hero_zcu102/hero_zcu102.srcs/sources_1/bd/hero_zcu102/hero_zcu102.bd \
] -top
add_files -norecurse \
  ./hero_zcu102/hero_zcu102.srcs/sources_1/bd/hero_zcu102/hdl/hero_zcu102_wrapper.v

# Define include and defines again for PULP.
# TODO: This needs to be taken from one file.
set_property include_dirs [list \
    /scratch/andkurt/hero-v3/hardware/./deps/axi/include \
    /scratch/andkurt/hero-v3/hardware/./deps/cluster_interconnect/rtl/low_latency_interco \
    /scratch/andkurt/hero-v3/hardware/./deps/cluster_interconnect/rtl/peripheral_interco \
    /scratch/andkurt/hero-v3/hardware/./deps/cluster_peripherals/event_unit/include \
    /scratch/andkurt/hero-v3/hardware/./deps/common_cells/include \
    /scratch/andkurt/hero-v3/hardware/./deps/event_unit_flex \
    /scratch/andkurt/hero-v3/hardware/./deps/mchan/include \
    /scratch/andkurt/hero-v3/hardware/./deps/riscv/include \
    /scratch/andkurt/hero-v3/hardware/src/apb/include \
] [get_filesets hero_zcu102_pulp_zcu102_0_1]
set_property verilog_define [list \
    TARGET_FPGA \
    TARGET_SYNTHESIS \
    TARGET_VIVADO \
    TARGET_XILINX \
] [get_filesets hero_zcu102_pulp_zcu102_0_1]

# Synthesize
launch_runs synth_1 -jobs 12
wait_on_run synth_1

# Implement and Generate Bitstream
launch_runs impl_1 -to_step write_bitstream -jobs 12
wait_on_run impl_1
