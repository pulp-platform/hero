// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

interface BBMUX_CONFIG_BUS;

  logic [3:0][1:0] bbmux_tcdm;
  logic [3:0][1:0] bbmux_core;
  logic      [1:0] bbmux_scm;
  logic      [1:0] bbmux_int;
  logic            bbmux_sel;

  modport Master (
    output bbmux_tcdm, bbmux_core, bbmux_scm, bbmux_int, bbmux_sel
  );

  modport Slave (
    input bbmux_tcdm, bbmux_core, bbmux_scm, bbmux_int, bbmux_sel
  );

endinterface
