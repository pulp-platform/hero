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

module axi2mem
#(
   parameter PER_ADDR_WIDTH = 32,
   parameter PER_ID_WIDTH   = 5,
   parameter AXI_ADDR_WIDTH = 32,
   parameter AXI_DATA_WIDTH = 64,
   parameter AXI_USER_WIDTH = 6,
   parameter AXI_ID_WIDTH   = 3,
   parameter BUFFER_DEPTH   = 2,
   parameter AXI_STRB_WIDTH = AXI_DATA_WIDTH/8
)
(
   input  logic                      clk_i,
   input  logic                      rst_ni,
   input  logic                      test_en_i,

   // AXI4 SLAVE
   //***************************************
   // WRITE ADDRESS CHANNEL
   input  logic                      axi_slave_aw_valid_i,
   input  logic [AXI_ADDR_WIDTH-1:0] axi_slave_aw_addr_i,
   input  logic [2:0]                axi_slave_aw_prot_i,
   input  logic [3:0]                axi_slave_aw_region_i,
   input  logic [7:0]                axi_slave_aw_len_i,
   input  logic [2:0]                axi_slave_aw_size_i,
   input  logic [1:0]                axi_slave_aw_burst_i,
   input  logic                      axi_slave_aw_lock_i,
   input  logic [5:0]                axi_slave_aw_atop_i,
   input  logic [3:0]                axi_slave_aw_cache_i,
   input  logic [3:0]                axi_slave_aw_qos_i,
   input  logic [AXI_ID_WIDTH-1:0]   axi_slave_aw_id_i,
   input  logic [AXI_USER_WIDTH-1:0] axi_slave_aw_user_i,
   output logic                      axi_slave_aw_ready_o,

   // READ ADDRESS CHANNEL
   input  logic                      axi_slave_ar_valid_i,
   input  logic [AXI_ADDR_WIDTH-1:0] axi_slave_ar_addr_i,
   input  logic [2:0]                axi_slave_ar_prot_i,
   input  logic [3:0]                axi_slave_ar_region_i,
   input  logic [7:0]                axi_slave_ar_len_i,
   input  logic [2:0]                axi_slave_ar_size_i,
   input  logic [1:0]                axi_slave_ar_burst_i,
   input  logic                      axi_slave_ar_lock_i,
   input  logic [3:0]                axi_slave_ar_cache_i,
   input  logic [3:0]                axi_slave_ar_qos_i,
   input  logic [AXI_ID_WIDTH-1:0]   axi_slave_ar_id_i,
   input  logic [AXI_USER_WIDTH-1:0] axi_slave_ar_user_i,
   output logic                      axi_slave_ar_ready_o,

   // WRITE DATA CHANNEL
   input  logic                      axi_slave_w_valid_i,
   input  logic [AXI_DATA_WIDTH-1:0] axi_slave_w_data_i,
   input  logic [AXI_STRB_WIDTH-1:0] axi_slave_w_strb_i,
   input  logic [AXI_USER_WIDTH-1:0] axi_slave_w_user_i,
   input  logic                      axi_slave_w_last_i,
   output logic                      axi_slave_w_ready_o,

   // READ DATA CHANNEL
   output logic                      axi_slave_r_valid_o,
   output logic [AXI_DATA_WIDTH-1:0] axi_slave_r_data_o,
   output logic [1:0]                axi_slave_r_resp_o,
   output logic                      axi_slave_r_last_o,
   output logic [AXI_ID_WIDTH-1:0]   axi_slave_r_id_o,
   output logic [AXI_USER_WIDTH-1:0] axi_slave_r_user_o,
   input  logic                      axi_slave_r_ready_i,

   // WRITE RESPONSE CHANNEL
   output logic                      axi_slave_b_valid_o,
   output logic [1:0]                axi_slave_b_resp_o,
   output logic [AXI_ID_WIDTH-1:0]   axi_slave_b_id_o,
   output logic [AXI_USER_WIDTH-1:0] axi_slave_b_user_o,
   input  logic                      axi_slave_b_ready_i,

   // TCDM MASTER
   //***************************************
   // REQUEST CHANNEL
   output logic [3:0]                tcdm_master_req_o,
   output logic [3:0][31:0]          tcdm_master_add_o,
   output logic [3:0]                tcdm_master_type_o,
   output logic [3:0][3:0]           tcdm_master_be_o,
   output logic [3:0][31:0]          tcdm_master_data_o,
   input  logic [3:0]                tcdm_master_gnt_i,

   // RESPONSE CHANNEL
   input  logic [3:0]                tcdm_master_r_valid_i,
   input  logic [3:0][31:0]          tcdm_master_r_data_i,

   // BUSY SIGNAL
   output logic                      busy_o
);
   
   // SIGNAL DECLARATION
   logic                              s_aw_valid;
   logic [AXI_ADDR_WIDTH-1:0]         s_aw_addr;
   logic [2:0]                        s_aw_prot;
   logic [3:0]                        s_aw_region;
   logic [7:0]                        s_aw_len;
   logic [2:0]                        s_aw_size;
   logic [1:0]                        s_aw_burst;
   logic                              s_aw_lock;
   logic [5:0]                        s_aw_atop;
   logic [3:0]                        s_aw_cache;
   logic [3:0]                        s_aw_qos;
   logic [AXI_ID_WIDTH-1:0]           s_aw_id;
   logic [AXI_USER_WIDTH-1:0]         s_aw_user;
   logic                              s_aw_ready;
   
   logic                              s_ar_valid;
   logic [AXI_ADDR_WIDTH-1:0]         s_ar_addr;
   logic [2:0]                        s_ar_prot;
   logic [3:0]                        s_ar_region;
   logic [7:0]                        s_ar_len;
   logic [2:0]                        s_ar_size;
   logic [1:0]                        s_ar_burst;
   logic                              s_ar_lock;
   logic [3:0]                        s_ar_cache;
   logic [3:0]                        s_ar_qos;
   logic [AXI_ID_WIDTH-1:0]           s_ar_id;
   logic [AXI_USER_WIDTH-1:0]         s_ar_user;
   logic                              s_ar_ready;
   
   logic                              s_w_valid;
   logic [AXI_DATA_WIDTH-1:0]         s_w_data;
   logic [AXI_STRB_WIDTH-1:0]         s_w_strb;
   logic [AXI_USER_WIDTH-1:0]         s_w_user;
   logic                              s_w_last;
   logic                              s_w_ready;
   
   logic                              s_r_valid;
   logic [AXI_DATA_WIDTH-1:0]         s_r_data;
   logic [1:0]                        s_r_resp;
   logic                              s_r_last;
   logic [AXI_ID_WIDTH-1:0]           s_r_id;
   logic [AXI_USER_WIDTH-1:0]         s_r_user;
   logic                              s_r_ready;
   
   logic                              s_b_valid;
   logic [1:0]                        s_b_resp;
   logic [AXI_ID_WIDTH-1:0]           s_b_id;
   logic [AXI_USER_WIDTH-1:0]         s_b_user;
   logic                              s_b_ready;
   
   logic [1:0]                        s_trans_wr_req,s_trans_rd_req;
   logic [1:0][3:0]                   s_trans_rd_be;
   logic [1:0][5:0]                   s_trans_wr_id,s_trans_rd_id;
   logic [1:0][31:0]                  s_trans_wr_add,s_trans_rd_add;
   logic [1:0]                        s_trans_wr_last,s_trans_rd_last;
   logic [1:0]                        s_trans_wr_gnt,s_trans_rd_gnt;
   
   logic [1:0]                        s_rd_data_push_req, s_rd_data_push_gnt, s_wr_data_pop_req, s_wr_data_pop_gnt;
   logic [1:0][31:0]                  s_rd_data_push_dat, s_wr_data_pop_dat;
   logic [1:0][3:0]                   s_rd_data_push_strb, s_wr_data_pop_strb;
   logic [5:0]                        s_rd_data_push_id,s_rd_data_pop_id;
   logic                              s_wr_data_push_gnt, s_rd_data_pop_req, s_wr_data_push_req, s_rd_data_pop_gnt, s_rd_data_push_last, s_rd_data_pop_last;
   logic [63:0]                       s_wr_data_push_dat, s_rd_data_pop_dat;
   logic [7:0]                        s_wr_data_push_strb, s_rd_data_pop_strb;
   
   logic                              s_wr_trans_r_req;
   logic                              s_wr_trans_r_gnt;
   logic [5:0]                        s_wr_trans_r_id;
   
   // AXI2MEM REQUEST CHANNEL
   axi2mem_wr_channel
   #(
      .AXI_ADDR_WIDTH         ( AXI_ADDR_WIDTH      ),
      .AXI_DATA_WIDTH         ( AXI_DATA_WIDTH      ),
      .AXI_USER_WIDTH         ( AXI_USER_WIDTH      ),
      .AXI_ID_WIDTH           ( AXI_ID_WIDTH        )
   )
   wr_channel_i
   (
      .clk_i                  ( clk_i               ),
      .rst_ni                 ( rst_ni              ),
      .test_en_i              ( test_en_i           ),

      .axi_slave_aw_valid_i   ( s_aw_valid          ),
      .axi_slave_aw_addr_i    ( s_aw_addr           ),
      .axi_slave_aw_prot_i    ( s_aw_prot           ),
      .axi_slave_aw_region_i  ( s_aw_region         ),
      .axi_slave_aw_len_i     ( s_aw_len            ),
      .axi_slave_aw_size_i    ( s_aw_size           ),
      .axi_slave_aw_burst_i   ( s_aw_burst          ),
      .axi_slave_aw_lock_i    ( s_aw_lock           ),
      .axi_slave_aw_atop_i    ( s_aw_atop           ),
      .axi_slave_aw_cache_i   ( s_aw_cache          ),
      .axi_slave_aw_qos_i     ( s_aw_qos            ),
      .axi_slave_aw_id_i      ( s_aw_id             ),
      .axi_slave_aw_user_i    ( s_aw_user           ),
      .axi_slave_aw_ready_o   ( s_aw_ready          ),

      .axi_slave_w_valid_i    ( s_w_valid           ),
      .axi_slave_w_data_i     ( s_w_data            ),
      .axi_slave_w_strb_i     ( s_w_strb            ),
      .axi_slave_w_user_i     ( s_w_user            ),
      .axi_slave_w_last_i     ( s_w_last            ),
      .axi_slave_w_ready_o    ( s_w_ready           ),

      .axi_slave_b_valid_o    ( s_b_valid           ),
      .axi_slave_b_resp_o     ( s_b_resp            ),
      .axi_slave_b_id_o       ( s_b_id              ),
      .axi_slave_b_user_o     ( s_b_user            ),
      .axi_slave_b_ready_i    ( s_b_ready           ),

      .trans_req_o            ( s_trans_wr_req      ),
      .trans_id_o             ( s_trans_wr_id       ),
      .trans_add_o            ( s_trans_wr_add      ),
      .trans_last_o           ( s_trans_wr_last     ),
      .trans_gnt_i            ( s_trans_wr_gnt      ),

      .trans_r_id_i           ( s_wr_trans_r_id     ),
      .trans_r_req_i          ( s_wr_trans_r_req    ),
      .trans_r_gnt_o          ( s_wr_trans_r_gnt    ),

      .data_dat_o             ( s_wr_data_push_dat  ),
      .data_strb_o            ( s_wr_data_push_strb ),
      .data_req_o             ( s_wr_data_push_req  ),
      .data_gnt_i             ( s_wr_data_push_gnt  )
   );
   
   // AXI2MEM READ CHANNEL
   axi2mem_rd_channel
   #(
      .PER_ADDR_WIDTH         ( PER_ADDR_WIDTH      ),
      .AXI_ADDR_WIDTH         ( AXI_ADDR_WIDTH      ),
      .AXI_DATA_WIDTH         ( AXI_DATA_WIDTH      ),
      .AXI_USER_WIDTH         ( AXI_USER_WIDTH      ),
      .AXI_ID_WIDTH           ( AXI_ID_WIDTH        )
   )
   rd_channel_i
   (
      .clk_i                  ( clk_i               ),
      .rst_ni                 ( rst_ni              ),
      .test_en_i              ( test_en_i           ),

      .axi_slave_ar_valid_i   ( s_ar_valid          ),
      .axi_slave_ar_addr_i    ( s_ar_addr           ),
      .axi_slave_ar_prot_i    ( s_ar_prot           ),
      .axi_slave_ar_region_i  ( s_ar_region         ),
      .axi_slave_ar_len_i     ( s_ar_len            ),
      .axi_slave_ar_size_i    ( s_ar_size           ),
      .axi_slave_ar_burst_i   ( s_ar_burst          ),
      .axi_slave_ar_lock_i    ( s_ar_lock           ),
      .axi_slave_ar_cache_i   ( s_ar_cache          ),
      .axi_slave_ar_qos_i     ( s_ar_qos            ),
      .axi_slave_ar_id_i      ( s_ar_id             ),
      .axi_slave_ar_user_i    ( s_ar_user           ),
      .axi_slave_ar_ready_o   ( s_ar_ready          ),

      .axi_slave_r_valid_o    ( s_r_valid           ),
      .axi_slave_r_data_o     ( s_r_data            ),
      .axi_slave_r_resp_o     ( s_r_resp            ),
      .axi_slave_r_last_o     ( s_r_last            ),
      .axi_slave_r_id_o       ( s_r_id              ),
      .axi_slave_r_user_o     ( s_r_user            ),
      .axi_slave_r_ready_i    ( s_r_ready           ),

      .trans_id_o             ( s_trans_rd_id       ),
      .trans_add_o            ( s_trans_rd_add      ),
      .trans_be_o             ( s_trans_rd_be       ),
      .trans_req_o            ( s_trans_rd_req      ),
      .trans_last_o           ( s_trans_rd_last     ),
      .trans_gnt_i            ( s_trans_rd_gnt      ),

      .data_dat_i             ( s_rd_data_pop_dat   ),
      .data_id_i              ( s_rd_data_pop_id    ),
      .data_last_i            ( s_rd_data_pop_last  ),
      .data_req_o             ( s_rd_data_pop_req   ),
      .data_gnt_i             ( s_rd_data_pop_gnt   )
   );
   
   //**********************************************************
   //*************** TRANSACTIONS BUFFER **********************
   //********************************************************** 
   axi2mem_trans_unit trans_unit_i
   (
      .clk_i               ( clk_i                ),
      .rst_ni              ( rst_ni               ),
      .test_en_i           ( test_en_i            ),

      .rd_data_push_dat_i  ( s_rd_data_push_dat   ),
      .rd_data_push_req_i  ( s_rd_data_push_req   ),
      .rd_data_push_gnt_o  ( s_rd_data_push_gnt   ),
      .rd_data_push_id_i   ( s_rd_data_push_id    ),
      .rd_data_push_last_i ( s_rd_data_push_last  ),

      .rd_data_pop_dat_o   ( s_rd_data_pop_dat    ),
      .rd_data_pop_req_i   ( s_rd_data_pop_req    ),
      .rd_data_pop_gnt_o   ( s_rd_data_pop_gnt    ),
      .rd_data_pop_id_o    ( s_rd_data_pop_id     ),
      .rd_data_pop_last_o  ( s_rd_data_pop_last   ),

      .wr_data_push_dat_i  ( s_wr_data_push_dat   ),
      .wr_data_push_strb_i ( s_wr_data_push_strb  ),
      .wr_data_push_req_i  ( s_wr_data_push_req   ),
      .wr_data_push_gnt_o  ( s_wr_data_push_gnt   ),

      .wr_data_pop_dat_o   ( s_wr_data_pop_dat    ),
      .wr_data_pop_strb_o  ( s_wr_data_pop_strb   ),
      .wr_data_pop_req_i   ( s_wr_data_pop_req    ),
      .wr_data_pop_gnt_o   ( s_wr_data_pop_gnt    )
   );
   
   //**********************************************************
   //*************** TCDM UNIT ********************************
   //**********************************************************
   axi2mem_tcdm_unit tcdm_unit_i
   (
      .clk_i            ( clk_i                  ),
      .rst_ni           ( rst_ni                 ),
      .test_en_i        ( test_en_i              ),

      .tcdm_req_o       ( tcdm_master_req_o      ),
      .tcdm_add_o       ( tcdm_master_add_o      ),
      .tcdm_we_o        ( tcdm_master_type_o     ),
      .tcdm_be_o        ( tcdm_master_be_o       ),
      .tcdm_wdata_o     ( tcdm_master_data_o     ),
      .tcdm_gnt_i       ( tcdm_master_gnt_i      ),
      .tcdm_r_valid_i   ( tcdm_master_r_valid_i  ),
      .tcdm_r_rdata_i   ( tcdm_master_r_data_i   ),

      // WR CHANNEL
      .trans_wr_id_i    ( s_trans_wr_id          ),
      .trans_wr_add_i   ( s_trans_wr_add         ),
      .trans_wr_req_i   ( s_trans_wr_req         ),
      .trans_wr_last_i  ( s_trans_wr_last        ),
      .trans_wr_gnt_o   ( s_trans_wr_gnt         ),

      .data_wr_dat_i    ( s_wr_data_pop_dat      ),
      .data_wr_strb_i   ( s_wr_data_pop_strb     ),
      .data_wr_req_o    ( s_wr_data_pop_req      ),
      .data_wr_gnt_i    ( s_wr_data_pop_gnt      ),

      .synch_wr_gnt_i   ( s_wr_trans_r_gnt       ),
      .synch_wr_req_o   ( s_wr_trans_r_req       ),
      .synch_wr_id_o    ( s_wr_trans_r_id        ),

      // RD CHANNEL
      .trans_rd_id_i    ( s_trans_rd_id          ),
      .trans_rd_add_i   ( s_trans_rd_add         ),
      .trans_rd_last_i  ( s_trans_rd_last        ),
      .trans_rd_req_i   ( s_trans_rd_req         ),
      .trans_rd_be_i    ( s_trans_rd_be          ),
      .trans_rd_gnt_o   ( s_trans_rd_gnt         ),

      .data_rd_dat_o    ( s_rd_data_push_dat     ),
      .data_rd_last_o   ( s_rd_data_push_last    ),
      .data_rd_id_o     ( s_rd_data_push_id      ),
      .data_rd_req_o    ( s_rd_data_push_req     ),
      .data_rd_gnt_i    ( s_rd_data_push_gnt     )
   );
   
   //**********************************************************
   //*************** BUSY UNIT ********************************
   //**********************************************************
   axi2mem_busy_unit busy_unit_i
   (
      .clk_i       ( clk_i                             ),
      .rst_ni      ( rst_ni                            ),

      // WRITE INTERFACE
      .aw_sync_i   ( s_aw_valid & s_aw_ready           ),
      .b_sync_i    ( s_b_valid & s_b_ready             ),

      // READ INTERFACE
      .ar_sync_i   ( s_ar_valid & s_ar_ready           ),
      .r_sync_i    ( s_r_valid & s_r_ready & s_r_last  ),

      // BUSY SIGNAL
      .busy_o      ( busy_o                            )
   );
      
   //**********************************************************
   //*************** AXI BUFFERS ******************************
   //**********************************************************
   
   // AXI WRITE ADDRESS CHANNEL BUFFER
   axi_aw_buffer
   #(
      .ID_WIDTH       ( AXI_ID_WIDTH            ),
      .ADDR_WIDTH     ( AXI_ADDR_WIDTH          ),
      .USER_WIDTH     ( AXI_USER_WIDTH          ),
      .BUFFER_DEPTH   ( BUFFER_DEPTH            )
   )
   aw_buffer_i
   (
      .clk_i           ( clk_i                  ),
      .rst_ni          ( rst_ni                 ),
      .test_en_i       ( test_en_i              ),

      .slave_valid_i   ( axi_slave_aw_valid_i   ),
      .slave_addr_i    ( axi_slave_aw_addr_i    ),
      .slave_prot_i    ( axi_slave_aw_prot_i    ),
      .slave_region_i  ( axi_slave_aw_region_i  ),
      .slave_len_i     ( axi_slave_aw_len_i     ),
      .slave_size_i    ( axi_slave_aw_size_i    ),
      .slave_burst_i   ( axi_slave_aw_burst_i   ),
      .slave_lock_i    ( axi_slave_aw_lock_i    ),
      .slave_atop_i    ( axi_slave_aw_atop_i    ),
      .slave_cache_i   ( axi_slave_aw_cache_i   ),
      .slave_qos_i     ( axi_slave_aw_qos_i     ),
      .slave_id_i      ( axi_slave_aw_id_i      ),
      .slave_user_i    ( axi_slave_aw_user_i    ),
      .slave_ready_o   ( axi_slave_aw_ready_o   ),

      .master_valid_o  ( s_aw_valid             ),
      .master_addr_o   ( s_aw_addr              ),
      .master_prot_o   ( s_aw_prot              ),
      .master_region_o ( s_aw_region            ),
      .master_len_o    ( s_aw_len               ),
      .master_size_o   ( s_aw_size              ),
      .master_burst_o  ( s_aw_burst             ),
      .master_lock_o   ( s_aw_lock              ),
      .master_atop_o   ( s_aw_atop              ),
      .master_cache_o  ( s_aw_cache             ),
      .master_qos_o    ( s_aw_qos               ),
      .master_id_o     ( s_aw_id                ),
      .master_user_o   ( s_aw_user              ),
      .master_ready_i  ( s_aw_ready             )
   );
   
   // AXI READ ADDRESS CHANNEL BUFFER
   axi_ar_buffer
   #(
      .ID_WIDTH        ( AXI_ID_WIDTH           ),
      .ADDR_WIDTH      ( AXI_ADDR_WIDTH         ),
      .USER_WIDTH      ( AXI_USER_WIDTH         ),
      .BUFFER_DEPTH    ( BUFFER_DEPTH           )
   )
   ar_buffer_i
   (
      .clk_i           ( clk_i                  ),
      .rst_ni          ( rst_ni                 ),
      .test_en_i       ( test_en_i              ),

      .slave_valid_i   ( axi_slave_ar_valid_i   ),
      .slave_addr_i    ( axi_slave_ar_addr_i    ),
      .slave_prot_i    ( axi_slave_ar_prot_i    ),
      .slave_region_i  ( axi_slave_ar_region_i  ),
      .slave_len_i     ( axi_slave_ar_len_i     ),
      .slave_size_i    ( axi_slave_ar_size_i    ),
      .slave_burst_i   ( axi_slave_ar_burst_i   ),
      .slave_lock_i    ( axi_slave_ar_lock_i    ),
      .slave_cache_i   ( axi_slave_ar_cache_i   ),
      .slave_qos_i     ( axi_slave_ar_qos_i     ),
      .slave_id_i      ( axi_slave_ar_id_i      ),
      .slave_user_i    ( axi_slave_ar_user_i    ),
      .slave_ready_o   ( axi_slave_ar_ready_o   ),

      .master_valid_o  ( s_ar_valid             ),
      .master_addr_o   ( s_ar_addr              ),
      .master_prot_o   ( s_ar_prot              ),
      .master_region_o ( s_ar_region            ),
      .master_len_o    ( s_ar_len               ),
      .master_size_o   ( s_ar_size              ),
      .master_burst_o  ( s_ar_burst             ),
      .master_lock_o   ( s_ar_lock              ),
      .master_cache_o  ( s_ar_cache             ),
      .master_qos_o    ( s_ar_qos               ),
      .master_id_o     ( s_ar_id                ),
      .master_user_o   ( s_ar_user              ),
      .master_ready_i  ( s_ar_ready             )
   );
   
   // AXI WRITE DATA CHANNEL BUFFER
   axi_w_buffer
   #(
      .DATA_WIDTH      ( AXI_DATA_WIDTH        ),
      .USER_WIDTH      ( AXI_USER_WIDTH        ),
      .BUFFER_DEPTH    ( BUFFER_DEPTH          )
   )
   w_buffer_i
   (
      .clk_i           ( clk_i                 ),
      .rst_ni          ( rst_ni                ),
      .test_en_i       ( test_en_i             ),

      .slave_valid_i   ( axi_slave_w_valid_i   ),
      .slave_data_i    ( axi_slave_w_data_i    ),
      .slave_strb_i    ( axi_slave_w_strb_i    ),
      .slave_user_i    ( axi_slave_w_user_i    ),
      .slave_last_i    ( axi_slave_w_last_i    ),
      .slave_ready_o   ( axi_slave_w_ready_o   ),

      .master_valid_o  ( s_w_valid             ),
      .master_data_o   ( s_w_data              ),
      .master_strb_o   ( s_w_strb              ),
      .master_user_o   ( s_w_user              ),
      .master_last_o   ( s_w_last              ),
      .master_ready_i  ( s_w_ready             )
   );
   
   // AXI READ DATA CHANNEL BUFFER
   axi_r_buffer
   #(
      .ID_WIDTH        ( AXI_ID_WIDTH         ),
      .DATA_WIDTH      ( AXI_DATA_WIDTH       ),
      .USER_WIDTH      ( AXI_USER_WIDTH       ),
      .BUFFER_DEPTH    ( BUFFER_DEPTH         )
   )
   r_buffer_i
   (
      .clk_i           ( clk_i                ),
      .rst_ni          ( rst_ni               ),
      .test_en_i       ( test_en_i            ),

      .slave_valid_i   ( s_r_valid            ),
      .slave_data_i    ( s_r_data             ),
      .slave_resp_i    ( s_r_resp             ),
      .slave_user_i    ( s_r_user             ),
      .slave_id_i      ( s_r_id               ),
      .slave_last_i    ( s_r_last             ),
      .slave_ready_o   ( s_r_ready            ),

      .master_valid_o  ( axi_slave_r_valid_o  ),
      .master_data_o   ( axi_slave_r_data_o   ),
      .master_resp_o   ( axi_slave_r_resp_o   ),
      .master_user_o   ( axi_slave_r_user_o   ),
      .master_id_o     ( axi_slave_r_id_o     ),
      .master_last_o   ( axi_slave_r_last_o   ),
      .master_ready_i  ( axi_slave_r_ready_i  )
   );
   
   // AXI WRITE RESPONSE CHANNEL BUFFER
   axi_b_buffer
   #(
      .ID_WIDTH        ( AXI_ID_WIDTH         ),
      .USER_WIDTH      ( AXI_USER_WIDTH       ),
      .BUFFER_DEPTH    ( BUFFER_DEPTH         )
   )
   b_buffer_i
   (
      .clk_i           ( clk_i                ),
      .rst_ni          ( rst_ni               ),
      .test_en_i       ( test_en_i            ),

      .slave_valid_i   ( s_b_valid            ),
      .slave_resp_i    ( s_b_resp             ),
      .slave_id_i      ( s_b_id               ),
      .slave_user_i    ( s_b_user             ),
      .slave_ready_o   ( s_b_ready            ),

      .master_valid_o  ( axi_slave_b_valid_o  ),
      .master_resp_o   ( axi_slave_b_resp_o   ),
      .master_id_o     ( axi_slave_b_id_o     ),
      .master_user_o   ( axi_slave_b_user_o   ),
      .master_ready_i  ( axi_slave_b_ready_i  )
   );
   
endmodule
