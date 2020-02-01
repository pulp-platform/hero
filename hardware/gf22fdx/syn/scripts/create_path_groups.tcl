group_path -name "RISCV_DATA_REQ" -through   [ list [get_ports gen_clusters[0].gen_cluster_sync.i_cluster/i_ooc/i_bound/CORE*core_region_i/*CORE/data_addr_o*   ] \
                                                    [get_ports gen_clusters[0].gen_cluster_sync.i_cluster/i_ooc/i_bound/CORE*core_region_i/*CORE/data_wdata_o*  ] \
                                                    [get_ports gen_clusters[0].gen_cluster_sync.i_cluster/i_ooc/i_bound/CORE*core_region_i/*CORE/data_we_o*     ] \
                                                    [get_ports gen_clusters[0].gen_cluster_sync.i_cluster/i_ooc/i_bound/CORE*core_region_i/*CORE/data_req_o*    ] \
                                                    [get_ports gen_clusters[0].gen_cluster_sync.i_cluster/i_ooc/i_bound/CORE*core_region_i/*CORE/data_be_o*     ] \
                                                    [get_ports gen_clusters[0].gen_cluster_sync.i_cluster/i_ooc/i_bound/CORE*core_region_i/*CORE/data_gnt_i*    ] \
                                              ] -weight 2.0

group_path -name "RISCV_DATA_RESP" -through  [ list [get_ports gen_clusters[0].gen_cluster_sync.i_cluster/i_ooc/i_bound/CORE*core_region_i/*CORE/data_rdata_i*   ] \
                                                    [get_ports gen_clusters[0].gen_cluster_sync.i_cluster/i_ooc/i_bound/CORE*core_region_i/*CORE/data_rvalid_i*  ] \
                                              ] -weight 2.0

group_path -name "RISCV_INSTR_REQ" -through   [ list [get_ports gen_clusters[0].gen_cluster_sync.i_cluster/i_ooc/i_bound/CORE*core_region_i/*CORE/instr_addr_o*  ] \
                                                     [get_ports gen_clusters[0].gen_cluster_sync.i_cluster/i_ooc/i_bound/CORE*core_region_i/*CORE/instr_req_o*   ] \
                                                     [get_ports gen_clusters[0].gen_cluster_sync.i_cluster/i_ooc/i_bound/CORE*core_region_i/*CORE/instr_gnt_i*   ] \
                                              ] -weight 2.0

group_path -name "RISCV_INSTR_RESP" -through  [ list [get_ports gen_clusters[0].gen_cluster_sync.i_cluster/i_ooc/i_bound/CORE*core_region_i/*CORE/instr_rdata_i* ] \
                                                     [get_ports gen_clusters[0].gen_cluster_sync.i_cluster/i_ooc/i_bound/CORE*core_region_i/*CORE/instr_rvalid_i*] \
                                              ] -weight 2.0

group_path -name "RISCV_EX_STAGE" -through gen_clusters[0].gen_cluster_sync.i_cluster/i_ooc/i_bound/CORE*core_region_i/*CORE/ex_stage_i/*

group_path -name "CLUSTER_FPU" -through gen_clusters[0].gen_cluster_sync.i_cluster/i_ooc/i_bound/gen_shared_fpu.i_shared_fpu_cluster/*fpu*
