// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

interface CLKGATE_CONFIG_BUS #(
  parameter int NB_CORES = 4
);

  logic [NB_CORES-1:0]  clkgate_tcdm;
  logic [NB_CORES-1:0]  clkgate_core;
  logic                 clkgate_scm;
  logic                 clkgate_int;
  logic                 clkgate_hwacc;
  logic                 clkgate_sel;

  modport Master (
    output clkgate_tcdm, clkgate_core, clkgate_scm, clkgate_int, clkgate_hwacc, clkgate_sel
  );

  modport Slave (
    input clkgate_tcdm, clkgate_core, clkgate_scm, clkgate_int, clkgate_hwacc, clkgate_sel
  );

endinterface
