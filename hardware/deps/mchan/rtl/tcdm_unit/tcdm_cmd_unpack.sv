// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Davide Rossi <davide.rossi@unibo.it>

module tcdm_cmd_unpack #(
  parameter TRANS_SID_WIDTH = 2,
  parameter TCDM_ADD_WIDTH  = 12,
  parameter TCDM_OPC_WIDTH  = 12,
  parameter MCHAN_LEN_WIDTH = 15
) (
  input  logic                            clk_i,
  input  logic                            rst_ni,

  input  logic [TCDM_OPC_WIDTH-1:0]       cmd_opc_i,
  input  logic [MCHAN_LEN_WIDTH-1:0]      cmd_len_i,
  input  logic [TCDM_ADD_WIDTH-1:0]       cmd_add_i,
  input  logic [TRANS_SID_WIDTH-1:0]      cmd_sid_i,
  input  logic                            cmd_req_i,
  output logic                            cmd_gnt_o,

  output logic [1:0][TCDM_OPC_WIDTH-1:0]  beat_opc_o,
  output logic [1:0][TCDM_ADD_WIDTH-1:0]  beat_add_o,
  output logic [1:0][TRANS_SID_WIDTH-1:0] beat_sid_o,
  output logic [1:0]                      beat_eop_o,
  output logic [1:0]                      beat_req_o,
  input  logic [1:0]                      beat_gnt_i
);

  // CMD QUEUE SIGNALS
  logic [TCDM_OPC_WIDTH-1:0]  s_cmd_opc_reg;
  logic [TRANS_SID_WIDTH-1:0] s_cmd_sid_reg;
  logic [TCDM_ADD_WIDTH-1:0]  s_cmd_add_reg;

  // BEATS SIGNALS
  logic                       s_beat_req;
  logic                       s_beat_eop;
  logic [TCDM_OPC_WIDTH-1:0]  s_beat_opc;
  logic [TCDM_ADD_WIDTH-1:0]  s_beat_add;
  logic [TRANS_SID_WIDTH-1:0] s_beat_sid;
  logic [8:0]                 s_beats_nb,
                              s_beats_nb_align,
                              s_beats_nb_reg,
                              s_beats_count;

  // TRANSACTION SIGNALS
  logic                       s_trans_complete;

  // FSM STATES SIGNALS
  enum `ifdef TARGET_SYNTHESIS logic [1:0] `endif { TRANS_IDLE, TRANS_RUN } CS, NS;

  //**********************************************************
  //********************* CONTROL ****************************
  //**********************************************************

  //COMPUTE NUMBER OF BEATS
  assign s_beats_nb = cmd_len_i >> 3;

  // ADJUST NUMBER OF BEATS ACCORDING TO ALIGNMENT
  always_comb begin
    if (cmd_add_i[2:0] + cmd_len_i[2:0] < 8) begin
      s_beats_nb_align = s_beats_nb;
    end else begin
      s_beats_nb_align = s_beats_nb + 1;
    end
  end

  //**********************************************************
  //***** SAMPLES THE OPCODE OF THE CURRENT COMMAND **********
  //**********************************************************

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      s_beats_nb_reg <= '0;
      s_cmd_opc_reg  <= '0;
      s_cmd_sid_reg  <= '0;
    end else if (cmd_req_i && cmd_gnt_o) begin
      s_beats_nb_reg <= s_beats_nb_align;
      s_cmd_opc_reg  <= cmd_opc_i;
      s_cmd_sid_reg  <= cmd_sid_i;
    end
  end

  //**********************************************************
  //****** COMPUTES THE CURRENT TCDM ADDRESS *****************
  //**********************************************************

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      s_cmd_add_reg <= '0;
    end else if (cmd_req_i && cmd_gnt_o) begin
      s_cmd_add_reg <= cmd_add_i + 8;
    end else if (s_beat_req && beat_gnt_i[0] && beat_gnt_i[1]) begin
      s_cmd_add_reg <= s_cmd_add_reg + 8;
    end
  end

  //**********************************************************
  //*********** COUNTER FOR NUMBER OF STBUS BEATS ************
  //**********************************************************

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      s_beats_count <= '0;
    end else if (s_beat_eop) begin
      s_beats_count <= '0;
    end else if (s_beat_req && beat_gnt_i[0] && beat_gnt_i[1]) begin
      s_beats_count <= s_beats_count + 1;
    end
  end

  assign s_trans_complete = (s_beats_count == s_beats_nb_reg);

  //**********************************************************
  //********** FINITE STATE MACHINE FOR CMD QUEUE ************
  //**********************************************************

  // UPDATE THE STATE
  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (!rst_ni) begin
      CS <= TRANS_IDLE;
    end else begin
      CS <= NS;
    end
  end

  // COMPUTE NEXT STATE
  always_comb begin
    cmd_gnt_o  = '1;
    s_beat_req = '0;
    s_beat_eop = '0;
    s_beat_opc = '0;
    s_beat_add = '0;
    s_beat_sid = '0;
    NS         = CS;

    case(CS)
      TRANS_IDLE: begin
        s_beat_opc = cmd_opc_i;
        s_beat_add = cmd_add_i;
        s_beat_sid = cmd_sid_i;

        if (cmd_req_i && beat_gnt_i[0] && beat_gnt_i[1]) begin
          s_beat_req = 1'b1;
          if (s_beats_nb_align == 9'd0) begin
            s_beat_eop = 1'b1;
          end else begin
            NS = TRANS_RUN;
          end
        end else begin
          cmd_gnt_o = 1'b0;
        end
      end

      TRANS_RUN: begin
        cmd_gnt_o  = 1'b0;
        s_beat_opc = s_cmd_opc_reg;
        s_beat_add = s_cmd_add_reg;
        s_beat_sid = s_cmd_sid_reg;
        if (beat_gnt_i[0] && beat_gnt_i[1]) begin
          s_beat_req      = 1'b1;
          if (s_beats_nb_reg == 9'd1 || s_trans_complete) begin
            s_beat_eop     = 1'b1;
            NS             = TRANS_IDLE;
          end
        end
      end

      default: NS = TRANS_IDLE;
    endcase
  end

  assign beat_opc_o[0] = s_beat_opc;
  assign beat_opc_o[1] = s_beat_opc;
  assign beat_add_o[0] = {s_beat_add[TCDM_ADD_WIDTH-1:3],3'b000};
  assign beat_add_o[1] = {s_beat_add[TCDM_ADD_WIDTH-1:3],3'b000} + 4;
  assign beat_sid_o[0] = s_beat_sid;
  assign beat_sid_o[1] = s_beat_sid;
  assign beat_eop_o[0] = s_beat_eop;
  assign beat_eop_o[1] = s_beat_eop;
  assign beat_req_o[0] = s_beat_req;
  assign beat_req_o[1] = s_beat_req;

endmodule
