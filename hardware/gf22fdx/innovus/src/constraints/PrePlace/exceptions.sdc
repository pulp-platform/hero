################
## Exceptions
################

set_propagated_clock [all_clocks]

# CORE MULTICYCLE PATH
set_multicycle_path 2 -setup -through [get_pins fc_subsystem_i/FC_CORE_lFC_CORE/id_stage_i_registers_i_riscv_register_file_i_mem_reg*/Q]
set_multicycle_path 1 -hold  -through [get_pins fc_subsystem_i/FC_CORE_lFC_CORE/id_stage_i_registers_i_riscv_register_file_i_mem_reg*/Q]
