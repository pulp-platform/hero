// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Igor Loi - igor.loi@unibo.it                               //
//                                                                            //
// Additional contributions by:                                               //
//                 Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                                                                            //
// Design Name:    Load Store Unit                                            //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Load Store Unit, used to eliminate multiple access during  //
//                 processor stalls, and to align bytes and halfwords         //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////


module riscv_load_store_unit
(
    input  logic         clk,
    input  logic         rst_n,

    // output to data memory
    output logic         data_req_o,
    input  logic         data_gnt_i,
    input  logic         data_rvalid_i,
    input  logic         data_err_i,

    output logic [31:0]  data_addr_o,
    output logic         data_we_o,
    output logic [3:0]   data_be_o,
    output logic [31:0]  data_wdata_o,
    input  logic [31:0]  data_rdata_i,

    // signals from ex stage
    input  logic         data_we_ex_i,         // write enable                      -> from ex stage
    input  logic [1:0]   data_type_ex_i,       // Data type word, halfword, byte    -> from ex stage
    input  logic [31:0]  data_wdata_ex_i,      // data to write to memory           -> from ex stage
    input  logic [1:0]   data_reg_offset_ex_i, // offset inside register for stores -> from ex stage
    input  logic [1:0]   data_sign_ext_ex_i,   // sign extension                    -> from ex stage

    output logic [31:0]  data_rdata_ex_o,      // requested data                    -> to ex stage
    input  logic         data_req_ex_i,        // data request                      -> from ex stage
    input  logic [31:0]  operand_a_ex_i,       // operand a from RF for address     -> from ex stage
    input  logic [31:0]  operand_b_ex_i,       // operand b from RF for address     -> from ex stage
    input  logic         addr_useincr_ex_i,    // use a + b or just a for address   -> from ex stage

    input  logic         data_misaligned_ex_i, // misaligned access in last ld/st   -> from ID/EX pipeline
    output logic         data_misaligned_o,    // misaligned access was detected    -> to controller

    input  logic [5:0]   data_atop_ex_i,       // atomic instructions signal        -> from ex stage
    output logic [5:0]   data_atop_o,          // atomic instruction signal         -> core output

    // stall signal
    output logic         lsu_ready_ex_o, // LSU ready for new data in EX stage
    output logic         lsu_ready_wb_o, // LSU ready for new data in WB stage

    input  logic         ex_valid_i,
    output logic         busy_o
);

  // Calculate shift amount for strobe and data for unaligned accesses.
  logic [1:0] shamt;
  always_comb begin
    shamt = operand_a_ex_i[1:0];
    if (addr_useincr_ex_i) begin
      shamt += operand_b_ex_i[1:0];
    end
  end

  // Compute byte enable.
  always_comb begin
    if (data_type_ex_i[1]) begin          // writing a single byte
      data_be_o =    1'b1;
    end else if (data_type_ex_i[0]) begin // writing a half word
      data_be_o =   2'b11;
    end else begin                        // writing a full word
      data_be_o = 4'b1111;
    end
    data_be_o <<= shamt;
    // Write or read the other part of the word during the second access of an unaligned access.
    // FIXME: will not work for 16 bit accesses
    if (data_misaligned_ex_i) begin
      data_be_o = ~data_be_o;
    end
  end

  // Latch properties of request to reconstruct response.
  logic [3:0] mask_d,     mask_q;
  logic [1:0] shamt_d,    shamt_q;
  logic [1:0] type_d,     type_q;
  logic [1:0] sign_ext_d, sign_ext_q,
              we_d,       we_q;
  always_comb begin
    mask_d      = mask_q;
    shamt_d     = shamt_q;
    sign_ext_d  = sign_ext_q;
    type_d      = type_q;
    we_d        = we_q;
    if (data_req_o && data_gnt_i) begin
      mask_d      = data_be_o;
      shamt_d     = shamt;
      sign_ext_d  = data_sign_ext_ex_i;
      type_d      = data_type_ex_i;
      we_d        = data_we_ex_i;
    end
  end

  // Rotate write data to the left by the shift amount.
  always_comb begin
    case (shamt)
      2'd0: data_wdata_o = data_wdata_ex_i;
      2'd1: data_wdata_o = {data_wdata_ex_i[23:0], data_wdata_ex_i[31:24]};
      2'd2: data_wdata_o = {data_wdata_ex_i[15:0], data_wdata_ex_i[31:16]};
      2'd3: data_wdata_o = {data_wdata_ex_i[ 7:0], data_wdata_ex_i[31: 8]};
    endcase
  end

  // Identify responses to misaligned accesses.
  enum logic [1:0] {
    RespRegular,    // response to regular, non-misaligned request
    RespMisaligned, // response to first request of a misaligned access -> misaligned response
    RespAligned     // response to second request of a misaligned access -> aligned response
  } resp_state_d, resp_state_q;
  always_comb begin
    resp_state_d = resp_state_q;
    if (data_req_o && data_gnt_i && data_misaligned_o) begin
      // When we request misaligned data, the next response is misaligned.
      resp_state_d = RespMisaligned;
    end else if (data_rvalid_i) begin
      // A response to the first request of a misaligned access means the next response is to the
      // second request.
      resp_state_d = (resp_state_q == RespMisaligned) ? RespAligned : RespRegular;
    end
  end

  // Reconstruct read data from read response.
  logic ext_bit;
  logic [31:0] rdata_d, rdata_q;
  always_comb begin
    rdata_d = rdata_q;
    if (data_rvalid_i) begin
      // Mask response with byte enable from request.
      rdata_d = data_rdata_i & {{8{mask_q[3]}}, {8{mask_q[2]}}, {8{mask_q[1]}}, {8{mask_q[0]}}};
      // Reconstruct misaligned response.
      case (resp_state_q)
        RespRegular,
        RespMisaligned: begin
          rdata_d = rdata_d >> 8*shamt_q;
        end
        RespAligned: begin
          rdata_d = (rdata_d << 8*(4 - shamt_q)) | rdata_q;
        end
      endcase
      unique case (sign_ext_q)
        2'b00: ext_bit = 1'b0; // extend with zeros
        2'b10: ext_bit = 1'b1; // extend with ones
        default: begin // extend with value of MSB
          casez (type_q)
            2'b1?:   ext_bit = rdata_d[7];  // single byte
            2'b01:   ext_bit = rdata_d[15]; // half word
            default: ext_bit = 1'bx;
          endcase
        end
      endcase
      if (type_q[1]) begin          // single byte
        rdata_d = {{24{ext_bit}}, rdata_d[ 7:0]};
      end else if (type_q[0]) begin // half word
        rdata_d = {{16{ext_bit}}, rdata_d[15:0]};
      end
    end
  end

  enum logic [1:0]  { IDLE, WAIT_RVALID, WAIT_RVALID_EX_STALL, IDLE_EX_STALL } CS, NS;

  // FSM
  always_comb
  begin
    NS             = CS;

    data_req_o     = 1'b0;

    lsu_ready_ex_o = 1'b1;
    lsu_ready_wb_o = 1'b1;

    case(CS)
      // starts from not active and stays in IDLE until request was granted
      IDLE:
      begin
        data_req_o = data_req_ex_i;

        if(data_req_ex_i) begin
          lsu_ready_ex_o = 1'b0;

          if(data_gnt_i) begin
            lsu_ready_ex_o = 1'b1;

            if (ex_valid_i)
              NS = WAIT_RVALID;
            else
              NS = WAIT_RVALID_EX_STALL;
          end

          if(data_err_i) begin
            lsu_ready_ex_o = 1'b1;
          end

        end
      end //~ IDLE

      // wait for rvalid in WB stage and send a new request if there is any
      WAIT_RVALID:
      begin
        lsu_ready_wb_o = 1'b0;

        if (data_rvalid_i) begin
          // we don't have to wait for anything here as we are the only stall
          // source for the WB stage
          lsu_ready_wb_o = 1'b1;

          data_req_o = data_req_ex_i;

          if (data_req_ex_i) begin
            lsu_ready_ex_o = 1'b0;

            if (data_gnt_i) begin
              lsu_ready_ex_o = 1'b1;

              if(ex_valid_i)
                NS = WAIT_RVALID;
              else
                NS = WAIT_RVALID_EX_STALL;
            end else begin
              if(data_err_i) begin
                lsu_ready_ex_o = 1'b1;
              end
              NS = IDLE;
            end
          end else begin
            if (data_rvalid_i) begin
              // no request, so go to IDLE
              NS = IDLE;
            end
          end
        end
      end

      // wait for rvalid while still in EX stage
      // we end up here when there was an EX stall, so in this cycle we just
      // wait and don't send new requests
      WAIT_RVALID_EX_STALL:
      begin
        data_req_o = 1'b0;

        if (data_rvalid_i) begin
          if (ex_valid_i) begin
            // we are done and can go back to idle
            // the data is safely stored already
            NS = IDLE;
          end else begin
            // we have to wait until ex_stall is deasserted
            NS = IDLE_EX_STALL;
          end
        end else begin
          // we didn't yet receive the rvalid, so we check the ex_stall
          // signal. If we are no longer stalled we can change to the "normal"
          // WAIT_RVALID state
          if (ex_valid_i)
            NS = WAIT_RVALID;
        end
      end

      IDLE_EX_STALL:
      begin
        // wait for us to be unstalled and then change back to IDLE state
        if (ex_valid_i) begin
          NS = IDLE;
        end
      end

      default: begin
        NS = IDLE;
      end
    endcase
  end

  // check for misaligned accesses that need a second memory access
  // If one is detected, this is signaled with data_misaligned_o to
  // the controller which selectively stalls the pipeline
  always_comb begin
    data_misaligned_o = 1'b0;
    if (data_req_ex_i && !data_misaligned_ex_i) begin
      data_misaligned_o =
             (data_type_ex_i == 2'b00 && data_addr_o[1:0] != 2'b00)   // misaligned word
          || (data_type_ex_i == 2'b01 && data_addr_o[1:0] == 2'b11);  // misaligned half word
    end
  end

  // generate address from operands
  always_comb begin
    data_addr_o = operand_a_ex_i;
    if (addr_useincr_ex_i) begin
      data_addr_o += operand_b_ex_i;
      if (data_misaligned_ex_i) begin
        data_addr_o &= 32'hFFFF_FFFC;
      end
    end
  end

  assign busy_o = (CS == WAIT_RVALID) || (CS == WAIT_RVALID_EX_STALL) || (CS == IDLE_EX_STALL) || (data_req_o == 1'b1);

  // output to register file
  assign data_rdata_ex_o = data_rvalid_i ? rdata_d : rdata_q;

  // output to data interface
  assign data_we_o        = data_we_ex_i;
  assign data_atop_o      = data_atop_ex_i;

  always_ff @(posedge clk, negedge rst_n) begin
    if (!rst_n) begin
      CS            <= IDLE;
      mask_q        <=   '0;
      rdata_q       <=   '0;
      resp_state_q  <= RespRegular;
      shamt_q       <=   '0;
      sign_ext_q    <=   '0;
      type_q        <=   '0;
      we_q          <= 1'b0;
    end else begin
      CS            <= NS;
      mask_q        <= mask_d;
      rdata_q       <= rdata_d;
      resp_state_q  <= resp_state_d;
      shamt_q       <= shamt_d;
      sign_ext_q    <= sign_ext_d;
      type_q        <= type_d;
      we_q          <= we_d;
    end
  end

  //////////////////////////////////////////////////////////////////////////////
  // Assertions
  //////////////////////////////////////////////////////////////////////////////

  `ifndef VERILATOR
    // make sure there is no new request when the old one is not yet completely done
    assert property (@(posedge clk) CS == WAIT_RVALID && data_gnt_i |-> data_rvalid_i)
        else $warning("It should not be possible to get a grant without an rvalid for the last request!");

    assert property (@(posedge clk) CS == IDLE |-> !data_rvalid_i)
        else $warning("There should be no rvalid when the LSU is idle!");

    // assert that the address does not contain X when request is sent
    assert property (@(posedge clk) data_req_o |-> !$isunknown(data_addr_o))
        else $warning("There has been a data request but the address is unknown!");
  `endif
endmodule
