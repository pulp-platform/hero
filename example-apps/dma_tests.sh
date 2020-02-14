#!/bin/bash 

export GEN_SLM_PATH=$(pwd)/../hardware/test/gen_slm_files.sh
export CI=1
export START_SIM_PATH=$(pwd)/../hardware/vsim/
export START_SIM=$(pwd)/start_sim.sh

pushd mchan_tests
make clean all PULP_APP_SRCS=testMCHAN_4k_crossing.c
popd
pushd ./../hardware/test 
rm -rf slm_files/* 
"$GEN_SLM_PATH" mchan_tests 
popd
pushd $(pwd)/../hardware/vsim/ 
./start_sim.sh
cp transcript ./../../example-apps/mchan_tests/transcript_testMCHAN_4k_crossing
popd

pushd mchan_tests
make clean all PULP_APP_SRCS=testMCHAN_basic.c
popd
pushd ./../hardware/test 
rm -rf slm_files/* 
"$GEN_SLM_PATH" mchan_tests 
popd
pushd $(pwd)/../hardware/vsim/ 
./start_sim.sh
cp transcript ./../../example-apps/mchan_tests/transcript_testMCHAN_basic
popd

pushd mchan_tests
make clean all PULP_APP_SRCS=testMCHAN_basic_FC_TCDM.c
popd
pushd ./../hardware/test 
rm -rf slm_files/* 
"$GEN_SLM_PATH" mchan_tests 
popd
pushd $(pwd)/../hardware/vsim/ 
./start_sim.sh
cp transcript ./../../example-apps/mchan_tests/transcript_testMCHAN_basic_FC_TCDM
popd

pushd mchan_tests
make clean all PULP_APP_SRCS=testMCHAN_multi_trans.c
popd
pushd ./../hardware/test 
rm -rf slm_files/*    
"$GEN_SLM_PATH" mchan_tests 
popd
pushd $(pwd)/../hardware/vsim/ 
./start_sim.sh
cp transcript ./../../example-apps/mchan_tests/transcript_testMCHAN_multi_trans
popd

pushd mchan_tests
make clean all PULP_APP_SRCS=testMCHAN_not_incremental.c
popd
pushd ./../hardware/test 
rm -rf slm_files/*     
"$GEN_SLM_PATH" mchan_tests 
popd
pushd $(pwd)/../hardware/vsim/ 
./start_sim.sh
cp transcript ./../../example-apps/mchan_tests/transcript_testMCHAN_not_incremental
popd

pushd mchan_tests
make clean all PULP_APP_SRCS=testMCHAN_pe_basic.c
popd
pushd ./../hardware/test 
rm -rf slm_files/*     
"$GEN_SLM_PATH" mchan_tests 
popd
pushd $(pwd)/../hardware/vsim/ 
./start_sim.sh
cp transcript ./../../example-apps/mchan_tests/transcript_testMCHAN_pe_basic
popd

pushd mchan_tests
make clean all PULP_APP_SRCS=testMCHAN_pe_fc_basic.c
popd
pushd ./../hardware/test 
rm -rf slm_files/*    
"$GEN_SLM_PATH" mchan_tests 
popd
pushd $(pwd)/../hardware/vsim/ 
./start_sim.sh
cp transcript ./../../example-apps/mchan_tests/transcript_testMCHAN_pe_fc_basic
popd

pushd mchan_tests
make clean all PULP_APP_SRCS=testMCHAN_TCDM2TCDM_tx_rx.c
popd
pushd ./../hardware/test 
rm -rf slm_files/*    
"$GEN_SLM_PATH" mchan_tests 
popd
pushd $(pwd)/../hardware/vsim/ 
./start_sim.sh
cp transcript ./../../example-apps/mchan_tests/transcript_testMCHAN_TCDM2TCDM_tx_rx
popd

pushd mchan_tests
make clean all PULP_APP_SRCS=testMCHAN_4k_crossing.c
popd
pushd ./../hardware/test 
rm -rf slm_files/*    
"$GEN_SLM_PATH" mchan_tests 
popd
pushd $(pwd)/../hardware/vsim/ 
./start_sim.sh
cp transcript ./../../example-apps/mchan_tests/transcript_testMCHAN_4k_crossing
popd

pushd mchan_tests
make clean all PULP_APP_SRCS=testMCHAN_unaligned.c
popd
pushd ./../hardware/test 
rm -rf slm_files/*      
"$GEN_SLM_PATH" mchan_tests 
popd
pushd $(pwd)/../hardware/vsim/ 
./start_sim.sh
cp transcript ./../../example-apps/mchan_tests/transcript_testMCHAN_unaligned
popd

pushd mchan_tests
make clean all PULP_APP_SRCS=testMCHAN_2D_ext_tcdm.c
popd
pushd ./../hardware/test 
rm -rf slm_files/*      
"$GEN_SLM_PATH" mchan_tests 
popd
pushd $(pwd)/../hardware/vsim/ 
./start_sim.sh
cp transcript ./../../example-apps/mchan_tests/transcript_testMCHAN_2D_ext_tcdm
popd
