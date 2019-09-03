// Copyright 2014-2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer   : Jeremy Constantin - jeremy.constantin@epfl.ch                 //
// Create Date: 2014-04-02                                                    //
// Design Name: ULPSoC                                                        //
// Module Name: mmu_config_unit                                               //
//                                                                            //
// cluster peripheral providing configuration registers for MMUs              //
////////////////////////////////////////////////////////////////////////////////

module mmu_config_unit (
  input logic           clk_i,
  input logic           rst_ni,
  XBAR_PERIPH_BUS.Slave speriph_slave,
  MMU_CONFIG_BUS.Master mmu_bus
);
       
`ifdef MMU_IMPLEMENTED

  enum `ifdef SYNTHESIS logic [1:0] `endif
    { TRANS_IDLE,
      TRANS_WRITE, TRANS_READ }
    trans_state_n, trans_state_r;

  logic [4:0] s_r_id_r, s_r_id_n;
  logic [3:0] s_size_r[2], s_size_n[2];
  logic s_idx_r, s_idx_n;

  // peripheral bus transfer FSM
  always_comb
  begin : TRANS_FSM
    // default assignments
    speriph_slave.r_rdata = 0;
    speriph_slave.r_valid = 0;
    speriph_slave.r_id    = 0;
    trans_state_n         = TRANS_IDLE;
    s_r_id_n              = s_r_id_r;
    s_size_n              = s_size_r;
    s_idx_n               = s_idx_r;
    
    case(trans_state_r)
      TRANS_IDLE: begin
        if (speriph_slave.req) begin
          // select either config reg 0x0000 (SRAM) or 0x0004 (SCM)
          automatic logic idx = speriph_slave.add[2];
          if (!speriph_slave.wen) begin // write
            if (speriph_slave.be[0])
              s_size_n[idx] = speriph_slave.wdata[3:0];
            trans_state_n = TRANS_WRITE;
          end else begin // read
            s_idx_n = idx;
            trans_state_n = TRANS_READ;
          end
          s_r_id_n = speriph_slave.id;
        end
      end

      TRANS_WRITE: begin
        speriph_slave.r_valid = 1;
        speriph_slave.r_id    = s_r_id_r;
        trans_state_n = TRANS_IDLE;
      end

      TRANS_READ: begin
        speriph_slave.r_rdata = s_size_r[s_idx_r];
        speriph_slave.r_valid = 1;
        speriph_slave.r_id    = s_r_id_r;
        trans_state_n = TRANS_IDLE;
      end

      default: begin
        trans_state_n = TRANS_IDLE;
      end
    endcase
  end

  // registers
  always_ff @(posedge clk_i, negedge rst_ni)
  begin
    if (!rst_ni) begin
      trans_state_r <= TRANS_IDLE;
      s_r_id_r      <= 0;
      s_size_r      <= {0, 0};
      s_idx_r       <= 0;
    end else begin
      trans_state_r <= trans_state_n;
      s_r_id_r      <= s_r_id_n;
      s_size_r      <= s_size_n;
      s_idx_r       <= s_idx_n;
    end
  end

  // binding of output signals
  assign speriph_slave.gnt   = 1;
  assign speriph_slave.r_opc = 0;
  assign mmu_bus.mmu_sram_seqsec_size = s_size_r[0];
  assign mmu_bus.mmu_scm_seqsec_size  = s_size_r[1];

`else
  // MMU not implemented
  assign speriph_slave.gnt     = 1;
  assign speriph_slave.r_rdata = 0;
  assign speriph_slave.r_opc   = 0;
  assign speriph_slave.r_id    = 0;
  assign speriph_slave.r_valid = 0;   
  assign mmu_bus.mmu_sram_seqsec_size = 0;
  assign mmu_bus.mmu_scm_seqsec_size  = 0;

`endif

endmodule

