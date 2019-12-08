// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`define TRYX_CTRL_ADDREXT_ADDR 32'h1020_0BF8
`define TRYX_CTRL_USER_ADDR 32'h1020_0BFC

module tryx_ctrl #(
  parameter int unsigned NB_CORES = 0,
  parameter int unsigned AXI_USER_WIDTH = 0,
  parameter type tryx_req_t = logic
  // Dependent parameters, do not override!
) (
  input  logic                      clk_i,
  input  logic                      rst_ni,

  output tryx_req_t [NB_CORES-1:0]  tryx_req_o,
  input  logic [NB_CORES-1:0]       axi_xresp_decerr_i,
  input  logic [NB_CORES-1:0]       axi_xresp_slverr_i,
  input  logic [NB_CORES-1:0]       axi_xresp_valid_i,

  input  logic [NB_CORES-1:0]       unaligned_i,
  XBAR_PERIPH_BUS.Slave             periph_data_slave[NB_CORES-1:0],
  XBAR_PERIPH_BUS.Master            periph_data_master[NB_CORES-1:0]
);

  for (genvar i = 0; i < NB_CORES; i++) begin : gen_tryx_ctrl
    tryx_req_t  tryx_d,       tryx_q;
    logic       rd_en_d,      rd_en_q,
                unaligned_d,  unaligned_q,
                wait_d,       wait_q,
                wr_en_d,      wr_en_q;
    logic [3:0] err_d,        err_q;

    // Forward address, write data, and byte-enable from master to slave port.
    assign periph_data_master[i].add = periph_data_slave[i].add;
    assign periph_data_master[i].be = periph_data_slave[i].be;
    assign periph_data_master[i].wdata = periph_data_slave[i].wdata;

    assign tryx_req_o[i] = tryx_q;

    // Handle requests.
    always_comb begin
      periph_data_master[i].req = 1'b0;
      periph_data_master[i].wen = 1'b0;
      periph_data_slave[i].gnt = 1'b0;
      rd_en_d = 1'b0;
      wr_en_d = 1'b0;

      if (periph_data_slave[i].req) begin
        if (tryx_q.addrext == '0 && (
            periph_data_slave[i].add == `TRYX_CTRL_USER_ADDR
            || periph_data_slave[i].add == `TRYX_CTRL_ADDREXT_ADDR
        )) begin // request to TRYX control
          // Grant request.
          periph_data_slave[i].gnt = 1'b1;
          if (!periph_data_slave[i].wen) begin
            wr_en_d = 1'b1;
          end else if (periph_data_slave[i].wen && !rd_en_q) begin
            rd_en_d = 1'b1;
          end
        end else begin // request beyond TRYX control
          // Feed request through.
          periph_data_master[i].wen = periph_data_slave[i].wen;
          periph_data_master[i].req = 1'b1;
          periph_data_slave[i].gnt  = periph_data_master[i].gnt;
        end
      end
    end

    // Handle responses.
    always_comb begin
      if (rd_en_q || wr_en_q) begin // last request was to TRYX control
        periph_data_slave[i].r_opc = 1'b0;
        periph_data_slave[i].r_rdata = {tryx_q.user, {{32-AXI_USER_WIDTH-4}{1'b0}}, err_q};
        periph_data_slave[i].r_valid = 1'b1;
      end else begin // last request was beyond TRYX control
        periph_data_slave[i].r_opc    = periph_data_master[i].r_opc;
        periph_data_slave[i].r_rdata  = periph_data_master[i].r_rdata;
        periph_data_slave[i].r_valid  = periph_data_master[i].r_valid;
      end
    end

    // Track unaligned accesses.
    always_comb begin
      unaligned_d = unaligned_q;
      if (periph_data_master[i].req && periph_data_master[i].gnt && unaligned_i[i]) begin
        unaligned_d = 1'b1;
      end
      if (periph_data_master[i].r_valid) begin
        unaligned_d = 1'b0;
      end
    end

    // Latch AXI error and clear it when TRYX control is read.
    logic [1:0] err;
    assign err = {axi_xresp_decerr_i[i], axi_xresp_slverr_i[i]};
    always_comb begin
      err_d = err_q;
      if (axi_xresp_valid_i[i]) begin
        // If access was unaligned, put error into [3:2] otherwise into [1:0].
        if (unaligned_q) begin
          err_d[3:2] = err;
        end else begin
          err_d[1:0] = err;
        end
      end else if (rd_en_q) begin
        err_d = '0;
      end
    end

    // Track outstanding requests beyond TRYX control.
    always_comb begin
      wait_d = wait_q;
      if (periph_data_master[i].req && periph_data_master[i].gnt) begin // sent request
        wait_d = 1'b1;
      end else if (wait_q && periph_data_master[i].r_valid) begin       // got response
        wait_d = 1'b0;
      end
    end

    // Update TRYX register(s) when they are written, and clear them after one external request.
    always_comb begin
      tryx_d = tryx_q;
      if (wr_en_d) begin
        case (periph_data_slave[i].add)
          `TRYX_CTRL_USER_ADDR: tryx_d.user = periph_data_slave[i].wdata[31:31-(AXI_USER_WIDTH-1)];
          `TRYX_CTRL_ADDREXT_ADDR: tryx_d.addrext = periph_data_slave[i].wdata;
        endcase
      end else if (wait_q && !wait_d && !unaligned_q) begin
        tryx_d = '0;
      end
    end

    // Registers
    always_ff @(posedge clk_i, negedge rst_ni) begin
      if (!rst_ni) begin
        rd_en_q     <= 1'b0;
        err_q       <=   '0;
        tryx_q      <= '{default: '0};
        unaligned_q <= 1'b0;
        wait_q      <= 1'b0;
        wr_en_q     <= 1'b0;
      end else begin
        rd_en_q     <= rd_en_d;
        err_q       <= err_d;
        tryx_q      <= tryx_d;
        unaligned_q <= unaligned_d;
        wait_q      <= wait_d;
        wr_en_q     <= wr_en_d;
      end
    end
  end

  `ifndef VERILATOR
  // pragma translate_off
    initial begin
      assert (NB_CORES > 0) else $fatal(1, "NB_CORES not set!");
    end
  // pragma translate_on
 `endif

endmodule
