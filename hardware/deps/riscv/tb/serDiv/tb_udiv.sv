// Copyright (c) 2019 ETH Zurich, University of Bologna
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

///////////////////////////////////////////////
// unsigned division test

// init
NumStim_T   = 6+1000;

TestName_T  = "udiv test";

AcqTrig_T     <= 1;
applWaitCyc(Clk_CI,2);
AcqTrig_T     <= 0;
applWaitCyc(Clk_CI,2);

///////////////////////////////////////////////
applWait(Clk_CI, OutVld_SO);

OpBSign_SI  = 0;
OpCode_SI   = 0;

OpA_T       = 100;
OpB_T       = 2;

OpA_DI      = OpA_T;
OpBShift_DI = 32-$clog2(OpB_T+1);
OpB_DI      = OpB_T << OpBShift_DI;
InVld_SI    = 1;

applWaitCyc(Clk_CI,1);
////////////////////
applWait(Clk_CI, OutVld_SO);

InVld_SI    = 0;

OpA_T       = 2**32-1;
OpB_T       = 1;

OpA_DI      = OpA_T;
OpBShift_DI = 32-$clog2(OpB_T+1);
OpB_DI      = OpB_T << OpBShift_DI;
InVld_SI    = 1;

applWaitCyc(Clk_CI,1);
////////////////////
applWait(Clk_CI, OutVld_SO);

InVld_SI    = 0;

OpA_T       = 1;
OpB_T       = 2**32-1;

OpA_DI      = OpA_T;
OpBShift_DI = 32-$clog2(OpB_T+1);
OpB_DI      = OpB_T << OpBShift_DI;
InVld_SI    = 1;

applWaitCyc(Clk_CI,1);
////////////////////
applWait(Clk_CI, OutVld_SO);

InVld_SI    = 0;

OpA_T       = 0;
OpB_T       = 5456;

OpA_DI      = OpA_T;
OpBShift_DI = 32-$clog2(OpB_T+1);
OpB_DI      = OpB_T << OpBShift_DI;
InVld_SI    = 1;

applWaitCyc(Clk_CI,1);
////////////////////
applWait(Clk_CI, OutVld_SO);

InVld_SI    = 0;

OpA_T       = 875;
OpB_T       = 0;

OpA_DI      = OpA_T;
OpBShift_DI = 32-$clog2(OpB_T+1);
OpB_DI      = OpB_T << OpBShift_DI;
InVld_SI    = 1;

applWaitCyc(Clk_CI,1);
////////////////////
applWait(Clk_CI, OutVld_SO);

InVld_SI    = 0;

OpA_T       = 0;
OpB_T       = 0;

OpA_DI      = OpA_T;
OpBShift_DI = 32-$clog2(OpB_T+1);
OpB_DI      = OpB_T << OpBShift_DI;
InVld_SI    = 1;

applWaitCyc(Clk_CI,1);
////////////////////
applWait(Clk_CI, OutVld_SO);
InVld_SI    = 0;


////////////////////
// a couple of random stimuli

for (k = 0; k < 1000; k++) begin

    ok = randomize(OpA_T) with {OpA_T>=0; OpA_T<=2**C_WIDTH-1;};
    ok = randomize(OpB_T) with {OpB_T>=0; OpB_T<=2**C_WIDTH-1;};

    OpA_DI      = OpA_T;
    OpBShift_DI = 32-$clog2(OpB_T+1);
    OpB_DI      = OpB_T << OpBShift_DI;
    InVld_SI    = 1;

    applWaitCyc(Clk_CI,1);
    applWait(Clk_CI, OutVld_SO);

    InVld_SI    = 0;

end

applWaitCyc(Clk_CI, 100);

///////////////////////////////////////////////
