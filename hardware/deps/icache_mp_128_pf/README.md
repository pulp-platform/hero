# Structure of the repo

 .
- DOC/ 
- README.md 
- RTL/ 
    - cache_controller_to_axi_128_PF.sv 
    - central_controller_128.sv 
    - icache_bank_mp_128.sv 
    - icache_bank_mp_PF.sv 
    - icache_top_mp_128_PF.sv 
    - merge_refill_cam_128_16.sv 
    - pf_miss_mux.sv 
    - prefetcher_if.sv 
- SIM/ 
- src_files.yml 
- TB/ 


#This repo depends on the follwing sub-repos:

- icache-intc : read only log interco
- common_cells: generic_fifo and generic_LSFR_8bit
- tech_cells_generic: cluster_clock_gating
- axi_slice: AR and R Slices 