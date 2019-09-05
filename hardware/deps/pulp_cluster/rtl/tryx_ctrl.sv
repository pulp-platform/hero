// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

`define TRYX_CTRL_BASE_ADDR 32'h1020_0BFC

module tryx_ctrl #(
  parameter int unsigned NB_CORES = 0,
  parameter int unsigned AXI_USER_WIDTH = 0,
  // Dependent parameters, do not override!
  localparam type axi_user_t = logic[AXI_USER_WIDTH-1:0]
) (
  input  logic                      clk_i,
  input  logic                      rst_ni,

  output axi_user_t [NB_CORES-1:0]  axi_axuser_o,
  input  logic [NB_CORES-1:0]       axi_xresp_slverr_i,
  input  logic [NB_CORES-1:0]       axi_xresp_valid_i,

  XBAR_PERIPH_BUS.Slave             periph_data_slave[NB_CORES-1:0],
  XBAR_PERIPH_BUS.Master            periph_data_master[NB_CORES-1:0]
);

  for (genvar i = 0; i < NB_CORES; i++) begin : gen_tryx_ctrl
    axi_user_t  user_d,   user_q;
    logic       rd_en_d,  rd_en_q,
                slverr_d, slverr_q,
                wait_d,   wait_q,
                wr_en_d,  wr_en_q;

    // Forward address, write data, and byte-enable from master to slave port.
    assign periph_data_master[i].add = periph_data_slave[i].add;
    assign periph_data_master[i].be = periph_data_slave[i].be;
    assign periph_data_master[i].wdata = periph_data_slave[i].wdata;

    assign axi_axuser_o[i] = user_q;

    // Handle requests.
    always_comb begin
      periph_data_master[i].req = 1'b0;
      periph_data_master[i].wen = 1'b0;
      rd_en_d = 1'b0;
      wr_en_d = 1'b0;

      if (periph_data_slave[i].req) begin
        if (periph_data_slave[i].add != `TRYX_CTRL_BASE_ADDR) begin // request beyond TRYX control
          // Feed request through.
          periph_data_master[i].wen = periph_data_slave[i].wen;
          periph_data_master[i].req = 1'b1;
          periph_data_slave[i].gnt  = periph_data_master[i].gnt;
        end else begin // request to TRYX control
          // Grant request.
          periph_data_slave[i].gnt = 1'b1;
          if (!periph_data_slave[i].wen) begin
            wr_en_d = 1'b1;
          end else if (periph_data_slave[i].wen && !rd_en_q) begin
            rd_en_d = 1'b1;
          end
        end
      end
    end

    // Handle responses.
    always_comb begin
      if (rd_en_q || wr_en_q) begin // last request was to TRYX control
        periph_data_slave[i].r_opc = 1'b0;
        periph_data_slave[i].r_rdata = {user_q, {{32-AXI_USER_WIDTH-1}{1'b0}}, slverr_q};
        periph_data_slave[i].r_valid = 1'b1;
      end else begin // last request was beyond TRYX control
        periph_data_slave[i].r_opc    = periph_data_master[i].r_opc;
        periph_data_slave[i].r_rdata  = periph_data_master[i].r_rdata;
        periph_data_slave[i].r_valid  = periph_data_master[i].r_valid;
      end
    end

    // Latch AXI slave error and clear it when TRYX control is read.
    always_comb begin
      slverr_d = slverr_q;
      if (axi_xresp_valid_i[i]) begin
        slverr_d = axi_xresp_slverr_i[i];
      end else if (rd_en_q) begin
        slverr_d = 1'b0;
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

    // Set user signal when TRYX control is written and clear it after one external request.
    always_comb begin
      user_d = user_q;
      if (wr_en_d) begin
        user_d = periph_data_slave[i].wdata[31:31-(AXI_USER_WIDTH-1)];
      end else if (wait_q && !wait_d) begin
        user_d = '0;
      end
    end

    // Registers
    always_ff @(posedge clk_i, negedge rst_ni) begin
      if (!rst_ni) begin
        rd_en_q   <= 1'b0;
        slverr_q  <= 1'b0;
        user_q    <=   '0;
        wait_q    <= 1'b0;
        wr_en_q   <= 1'b0;
      end else begin
        rd_en_q   <= rd_en_d;
        slverr_q  <= slverr_d;
        user_q    <= user_d;
        wait_q    <= wait_d;
        wr_en_q   <= wr_en_d;
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
