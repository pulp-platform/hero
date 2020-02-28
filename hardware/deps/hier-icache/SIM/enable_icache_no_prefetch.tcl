force -freeze sim:/tb/sh_req_disable   8'b00000_0000 0
force -freeze sim:/tb/sh_req_enable    8'b11111_1111 0
force -freeze sim:/tb/pri_bypass_req   8'b00000_0000 0

run 8us
force -freeze sim:/tb/pri_bypass_req   8'b11111_1111 0
run 7us
force -freeze sim:/tb/pri_bypass_req   8'b00000_0000 0

run 8us
force -freeze sim:/tb/pri_bypass_req   8'b11111_1111 0
run 7us
force -freeze sim:/tb/pri_bypass_req   8'b00000_0000 0

run 8us
force -freeze sim:/tb/pri_bypass_req   8'b11111_1111 0
run 7us
force -freeze sim:/tb/pri_bypass_req   8'b00000_0000 0

run 8us
force -freeze sim:/tb/pri_bypass_req   8'b11111_1111 0
run 7us
force -freeze sim:/tb/pri_bypass_req   8'b00000_0000 0

run 8us
force -freeze sim:/tb/pri_bypass_req   8'b11111_1111 0
run 7us
force -freeze sim:/tb/pri_bypass_req   8'b00000_0000 0

run 8us
force -freeze sim:/tb/pri_bypass_req   8'b11111_1111 0
run 7us
force -freeze sim:/tb/pri_bypass_req   8'b00000_0000 0

run 8us
force -freeze sim:/tb/pri_bypass_req   8'b11111_1111 0
run 7us
force -freeze sim:/tb/pri_bypass_req   8'b00000_0000 0

run 8us
force -freeze sim:/tb/pri_bypass_req   8'b11111_1111 0
run 7us
force -freeze sim:/tb/pri_bypass_req   8'b00000_0000 0
