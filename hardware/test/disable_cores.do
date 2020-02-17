# disable clk to core 1 to 7
force -freeze {sim:/pulp_tb/dut/gen_clusters[0]/gen_cluster_sync/i_cluster/i_ooc/i_bound/CORE[1]/core_region_i/clk_i} 1'h0 0
force -freeze {sim:/pulp_tb/dut/gen_clusters[0]/gen_cluster_sync/i_cluster/i_ooc/i_bound/CORE[2]/core_region_i/clk_i} 1'h0 0
force -freeze {sim:/pulp_tb/dut/gen_clusters[0]/gen_cluster_sync/i_cluster/i_ooc/i_bound/CORE[3]/core_region_i/clk_i} 1'h0 0
force -freeze {sim:/pulp_tb/dut/gen_clusters[0]/gen_cluster_sync/i_cluster/i_ooc/i_bound/CORE[4]/core_region_i/clk_i} 1'h0 0
force -freeze {sim:/pulp_tb/dut/gen_clusters[0]/gen_cluster_sync/i_cluster/i_ooc/i_bound/CORE[5]/core_region_i/clk_i} 1'h0 0
force -freeze {sim:/pulp_tb/dut/gen_clusters[0]/gen_cluster_sync/i_cluster/i_ooc/i_bound/CORE[6]/core_region_i/clk_i} 1'h0 0
force -freeze {sim:/pulp_tb/dut/gen_clusters[0]/gen_cluster_sync/i_cluster/i_ooc/i_bound/CORE[7]/core_region_i/clk_i} 1'h0 0