set ALL_SCM [vfind /designs/$DESIGN/ -subdesign *test_wrap*]
foreach_in_collection cell $ALL_SCM {
    puts " Setting UNGROUP false and .boundary_opto strict_no on all [get_object_name $cell] instances"
    set_db [get_db $cell .hinst] .ungroup_ok false 
    set_db $cell .boundary_opto strict_no
}

ungroup [get_cells rstgen_i]                             -flatten
ungroup [get_cells data_master_slice_i/*]                -flatten
ungroup [get_cells data_slave_slice_i/*]                 -flatten
ungroup [get_cells CORE[*].core_region_i/*_CORE/*]       -flatten
ungroup [get_cells CORE[*].core_region_i/core_demux_i/*] -flatten
ungroup [get_cells cluster_interconnect_wrap_i/*]        -flatten
ungroup [get_cells cluster_peripherals_i/*]              -flatten

ungroup [get_cells dmac_wrap_i/*]                        -flatten
ungroup [get_cells per2axi_wrap_i/*]                     -flatten
ungroup [get_cells axi2mem_wrap_i/*]                     -flatten
ungroup [get_cells axi2per_wrap_i/*]                     -flatten
ungroup [get_cells cluster_bus_wrap_i/*]                 -flatten
ungroup [get_cells u_event_dc/*]                         -flatten
ungroup [get_cells u_clustercg/*]                        -flatten

ungroup [get_cells axi_size_UPSIZE_32_64_wrap_i/*]       -flatten

ungroup [get_cells icache_top_i/PRI_ICACHE*/*]         -flatten
ungroup [get_cells icache_top_i/Main*/*]               -flatten
ungroup [get_cells icache_top_i/ICACHE_INTERC*/*]      -flatten
ungroup [get_cells icache_top_i/MULTI*/*]              -flatten
