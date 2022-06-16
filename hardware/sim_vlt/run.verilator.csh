verilator -sv +1800-2017ext+  --Mdir worklib  +define+SYNTHESIS +define+TARGET_SYNTHESIS   --assert --autoflush --sc +notimingchecks -Wall -Wno-BLKANDNBLK -Wno-LITENDIAN -Wno-CASEINCOMPLETE -Wno-CMPCONST -Wno-WIDTH -Wno-WIDTHCONCAT -Wno-UNSIGNED -Wno-UNOPTFLAT -Wno-fatal  -f vcode.f  --top-module top

verilator -sv +1800-2017ext+ --compiler gcc --prefix V-f --Mdir worklib --make cmake --coverage --trace --sc -x-assign fast -sv +1800-2017ext+ --assert --autoflush --sc +notimingchecks --top-module top -Wall -Wno-BLKANDNBLK -Wno-LITENDIAN -Wno-CASEINCOMPLETE -Wno-CMPCONST -Wno-WIDTH -Wno-WIDTHCONCAT -Wno-UNSIGNED -Wno-UNOPTFLAT -Wno-fatal -f vcode.f +define+SYNTHESIS +define+TARGET_SYNTHESIS

