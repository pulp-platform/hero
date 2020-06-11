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

module axi_memory #(
    parameter int unsigned AXI_ADDR_WIDTH    = 64,
    parameter int unsigned AXI_DATA_WIDTH    = 64,
    parameter int unsigned AXI_ID_WIDTH      = 10,
    parameter int unsigned AXI_USER_WIDTH    = 10,
    parameter int unsigned MEM_ADDR_WIDTH    = 20
) (
    input           clk_i,
    input           rst_ni,
    AXI_BUS.Slave   slv
);

    localparam int unsigned MEM_OFFSET_BITS = $clog2(AXI_DATA_WIDTH/8);

    // Signal declaration
    logic [AXI_DATA_WIDTH-1:0]      w_data, r_data;
    logic [AXI_ADDR_WIDTH-1:0]      addr, aw_addr, ar_addr;
    logic [AXI_DATA_WIDTH/8-1:0]    be;
    logic                           req, we, wen;

    AXI_BUS_DV #(
        .AXI_ADDR_WIDTH ( AXI_ADDR_WIDTH ),
        .AXI_DATA_WIDTH ( AXI_DATA_WIDTH ),
        .AXI_ID_WIDTH   ( AXI_ID_WIDTH   ),
        .AXI_USER_WIDTH ( AXI_USER_WIDTH )
    ) axi_mem_int(
        .clk_i          ( clk_i          )
    );

    assign aw_addr = {{MEM_OFFSET_BITS{1'b0}}, slv.aw_addr[AXI_ADDR_WIDTH-1:MEM_OFFSET_BITS]};
    assign ar_addr = {{MEM_OFFSET_BITS{1'b0}}, slv.ar_addr[AXI_ADDR_WIDTH-1:MEM_OFFSET_BITS]};

    // Memory
    generic_memory #(
      .ADDR_WIDTH   ( MEM_ADDR_WIDTH ),
      .DATA_WIDTH   ( AXI_DATA_WIDTH )
    ) i_mem (
      .CLK      ( clk_i                     ),
      .INITN    ( 1'b1                      ),

      .CEN      ( 1'b0                      ),
      .A        ( addr[MEM_ADDR_WIDTH-1:0]  ),
      .WEN      ( ~we                       ),
      .D        ( w_data                    ),
      .BEN      ( ~be                       ),

      .Q        ( r_data                    )
    );

    // Memory interface
    // New version
    // axi2mem #(
    //     .AXI_ID_WIDTH  (AXI_ID_WIDTH  ),
    //     .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
    //     .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
    //     .AXI_USER_WIDTH(AXI_USER_WIDTH)
    // ) i_axi2mem (
    //     .clk_i  ( clk_i       ),
    //     .rst_ni ( rst_ni      ),
    //     .slave  ( axi_mem_int ),
    //     .req_o  ( req         ),
    //     .we_o   ( we          ),
    //     .addr_o ( addr        ),
    //     .be_o   ( be          ),
    //     .data_o ( w_data      ),
    //     .data_i ( r_data      )
    // );

    // // Assign internal AXI bus to know the exact time the memory is written
    // //AXI write address bus --------------------------------------
    // assign axi_mem_int.aw_id     = slv.aw_id;
    // assign axi_mem_int.aw_addr   = {{MEM_OFFSET_BITS{1'b0}}, slv.aw_addr[AXI_ADDR_WIDTH-1:MEM_OFFSET_BITS]};
    // assign axi_mem_int.aw_len    = slv.aw_len;
    // assign axi_mem_int.aw_size   = slv.aw_size;
    // assign axi_mem_int.aw_burst  = slv.aw_burst;
    // assign axi_mem_int.aw_lock   = slv.aw_lock;
    // assign axi_mem_int.aw_cache  = slv.aw_cache;
    // assign axi_mem_int.aw_prot   = slv.aw_prot;
    // assign axi_mem_int.aw_region = slv.aw_region;
    // assign axi_mem_int.aw_user   = slv.aw_user;
    // assign axi_mem_int.aw_qos    = slv.aw_qos;
    // assign axi_mem_int.aw_valid  = slv.aw_valid;
    // assign slv.aw_ready          = axi_mem_int.aw_ready;
    // //AXI write data bus -----------------------------------------
    // assign axi_mem_int.w_data    = slv.w_data;
    // assign axi_mem_int.w_strb    = slv.w_strb;
    // assign axi_mem_int.w_last    = slv.w_last;
    // assign axi_mem_int.w_user    = slv.w_user;
    // assign axi_mem_int.w_valid   = slv.w_valid;
    // assign slv.w_ready   = axi_mem_int.w_ready;
    // //AXI write respons-------------------------------------------
    // assign slv.b_id     = axi_mem_int.b_id;
    // assign slv.b_resp   = axi_mem_int.b_resp;
    // assign slv.b_valid  = axi_mem_int.b_valid;
    // assign slv.b_user   = axi_mem_int.b_user;
    // assign axi_mem_int.b_ready   = slv.b_ready;
    // //AXI read address -------------------------------------------
    // assign axi_mem_int.ar_id     = slv.ar_id;
    // assign axi_mem_int.ar_addr   = {{MEM_OFFSET_BITS{1'b0}}, slv.ar_addr[AXI_ADDR_WIDTH-1:MEM_OFFSET_BITS]};
    // assign axi_mem_int.ar_len    = slv.ar_len;
    // assign axi_mem_int.ar_size   = slv.ar_size;
    // assign axi_mem_int.ar_burst  = slv.ar_burst;
    // assign axi_mem_int.ar_lock   = slv.ar_lock;
    // assign axi_mem_int.ar_cache  = slv.ar_cache;
    // assign axi_mem_int.ar_prot   = slv.ar_prot;
    // assign axi_mem_int.ar_region = slv.ar_region;
    // assign axi_mem_int.ar_user   = slv.ar_user;
    // assign axi_mem_int.ar_qos    = slv.ar_qos;
    // assign axi_mem_int.ar_valid  = slv.ar_valid;
    // assign slv.ar_ready  = axi_mem_int.ar_ready;
    // //AXI read data bus-------------------------------------------
    // assign slv.r_id      = axi_mem_int.r_id;
    // assign slv.r_data    = axi_mem_int.r_data;
    // assign slv.r_resp    = axi_mem_int.r_resp;
    // assign slv.r_last    = axi_mem_int.r_last;
    // assign slv.r_user    = axi_mem_int.r_user;
    // assign slv.r_valid   = axi_mem_int.r_valid;
    // assign axi_mem_int.r_ready   = slv.r_ready;

    // Old version
    axi_mem_if #(
        .AXI4_ID_WIDTH       ( AXI_ID_WIDTH   ),
        .AXI4_ADDRESS_WIDTH  ( AXI_ADDR_WIDTH ),
        .AXI4_WDATA_WIDTH    ( AXI_DATA_WIDTH ),
        .AXI4_RDATA_WIDTH    ( AXI_DATA_WIDTH ),
        .AXI4_USER_WIDTH     ( AXI_USER_WIDTH ),
        .BUFF_DEPTH_SLAVE    ( 16              )
    ) i_axi2mem (
        .ACLK       ( clk_i         ),
        .ARESETn    ( rst_ni        ),
        .test_en_i  ( 1'b0          ),
        .AWVALID_i  ( slv.aw_valid  ),
        .AWADDR_i   ( aw_addr       ),
        .AWPROT_i   ( slv.aw_prot   ),
        .AWREGION_i ( slv.aw_region ),
        .AWLEN_i    ( slv.aw_len    ),
        .AWSIZE_i   ( slv.aw_size   ),
        .AWBURST_i  ( slv.aw_burst  ),
        .AWLOCK_i   ( slv.aw_lock   ),
        .AWCACHE_i  ( slv.aw_cache  ),
        .AWQOS_i    ( slv.aw_qos    ),
        .AWID_i     ( slv.aw_id     ),
        .AWUSER_i   ( slv.aw_user   ),
        .AWREADY_o  ( slv.aw_ready  ),
        .ARVALID_i  ( slv.ar_valid  ),
        .ARADDR_i   ( ar_addr       ),
        .ARPROT_i   ( slv.ar_prot   ),
        .ARREGION_i ( slv.ar_region ),
        .ARLEN_i    ( slv.ar_len    ),
        .ARSIZE_i   ( slv.ar_size   ),
        .ARBURST_i  ( slv.ar_burst  ),
        .ARLOCK_i   ( slv.ar_lock   ),
        .ARCACHE_i  ( slv.ar_cache  ),
        .ARQOS_i    ( slv.ar_qos    ),
        .ARID_i     ( slv.ar_id     ),
        .ARUSER_i   ( slv.ar_user   ),
        .ARREADY_o  ( slv.ar_ready  ),
        .RVALID_o   ( slv.r_valid   ),
        .RDATA_o    ( slv.r_data    ),
        .RRESP_o    ( slv.r_resp    ),
        .RLAST_o    ( slv.r_last    ),
        .RID_o      ( slv.r_id      ),
        .RUSER_o    ( slv.r_user    ),
        .RREADY_i   ( slv.r_ready   ),
        .WVALID_i   ( slv.w_valid   ),
        .WDATA_i    ( slv.w_data    ),
        .WSTRB_i    ( slv.w_strb    ),
        .WLAST_i    ( slv.w_last    ),
        .WUSER_i    ( slv.w_user    ),
        .WREADY_o   ( slv.w_ready   ),
        .BVALID_o   ( slv.b_valid   ),
        .BRESP_o    ( slv.b_resp    ),
        .BID_o      ( slv.b_id      ),
        .BUSER_o    ( slv.b_user    ),
        .BREADY_i   ( slv.b_ready   ),
        .CEN        (               ),
        .WEN        ( wen           ),
        .A          ( addr          ),
        .D          ( w_data        ),
        .BE         ( be            ),
        .Q          ( r_data        )
    );
    assign we = ~wen;

    // Assign internal AXI bus to know the exact time the memory is written
    //AXI write address bus --------------------------------------
    assign axi_mem_int.aw_id     = i_axi2mem.AWID;
    assign axi_mem_int.aw_addr   = i_axi2mem.AWADDR;
    assign axi_mem_int.aw_len    = i_axi2mem.AWLEN;
    assign axi_mem_int.aw_size   = i_axi2mem.AWSIZE;
    assign axi_mem_int.aw_burst  = i_axi2mem.AWBURST;
    assign axi_mem_int.aw_lock   = i_axi2mem.AWLOCK;
    assign axi_mem_int.aw_cache  = i_axi2mem.AWCACHE;
    assign axi_mem_int.aw_prot   = i_axi2mem.AWPROT;
    assign axi_mem_int.aw_region = i_axi2mem.AWREGION;
    assign axi_mem_int.aw_user   = i_axi2mem.AWUSER;
    assign axi_mem_int.aw_qos    = i_axi2mem.AWQOS;
    assign axi_mem_int.aw_valid  = i_axi2mem.AWVALID;
    assign axi_mem_int.aw_ready  = i_axi2mem.AWREADY;
    //AXI write data bus ------------------------ ----------------
    assign axi_mem_int.w_data    = i_axi2mem.WDATA;
    assign axi_mem_int.w_strb    = i_axi2mem.WSTRB;
    assign axi_mem_int.w_last    = i_axi2mem.WLAST;
    assign axi_mem_int.w_user    = i_axi2mem.WUSER;
    assign axi_mem_int.w_valid   = i_axi2mem.WVALID;
    assign axi_mem_int.w_ready   = i_axi2mem.WREADY;
    //AXI write respons-------------------------------------------
    assign axi_mem_int.b_id      = i_axi2mem.BID;
    assign axi_mem_int.b_resp    = i_axi2mem.BRESP;
    assign axi_mem_int.b_valid   = i_axi2mem.BVALID;
    assign axi_mem_int.b_user    = i_axi2mem.BUSER;
    assign axi_mem_int.b_ready   = i_axi2mem.BREADY;
    //AXI read address -------------------------------------------
    assign axi_mem_int.ar_id     = i_axi2mem.ARID;
    assign axi_mem_int.ar_addr   = i_axi2mem.ARADDR;
    assign axi_mem_int.ar_len    = i_axi2mem.ARLEN;
    assign axi_mem_int.ar_size   = i_axi2mem.ARSIZE;
    assign axi_mem_int.ar_burst  = i_axi2mem.ARBURST;
    assign axi_mem_int.ar_lock   = i_axi2mem.ARLOCK;
    assign axi_mem_int.ar_cache  = i_axi2mem.ARCACHE;
    assign axi_mem_int.ar_prot   = i_axi2mem.ARPROT;
    assign axi_mem_int.ar_region = i_axi2mem.ARREGION;
    assign axi_mem_int.ar_user   = i_axi2mem.ARUSER;
    assign axi_mem_int.ar_qos    = i_axi2mem.ARQOS;
    assign axi_mem_int.ar_valid  = i_axi2mem.ARVALID;
    assign axi_mem_int.ar_ready  = i_axi2mem.ARREADY;
    //AXI read data bus-------------------------------------------
    assign axi_mem_int.r_id      = i_axi2mem.RID;
    assign axi_mem_int.r_data    = i_axi2mem.RDATA;
    assign axi_mem_int.r_resp    = i_axi2mem.RRESP;
    assign axi_mem_int.r_last    = i_axi2mem.RLAST;
    assign axi_mem_int.r_user    = i_axi2mem.RUSER;
    assign axi_mem_int.r_valid   = i_axi2mem.RVALID;
    assign axi_mem_int.r_ready   = i_axi2mem.RREADY;

endmodule
