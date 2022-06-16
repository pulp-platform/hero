verilator +1800-2017ext+sv +notimingchecks --exe --build -j --Mdir worklib  +define+SYNTHESIS +define+TARGET_SYNTHESIS \
    --assert --autoflush --sc  -Wall -Wno-BLKANDNBLK -Wno-LITENDIAN -Wno-CASEINCOMPLETE -Wno-CMPCONST -Wno-WIDTH -Wno-WIDTHCONCAT -Wno-UNSIGNED -Wno-UNOPTFLAT -Wno-fatal  -f vcode.f top.cpp --top-module top
