force -freeze sim:/tb/sh_req_disable   9'b00000_0000 0
force -freeze sim:/tb/sh_req_enable    9'b11111_1111 0
force -freeze sim:/tb/pri_bypass_req   9'b00000_0000 0
force -freeze sim:/tb/enable_l1_l15_prefetch   9'b11111_1111 0
force -freeze sim:/tb/special_core_icache      1'b1 0
