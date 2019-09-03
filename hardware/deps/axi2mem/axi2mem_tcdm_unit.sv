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

module axi2mem_tcdm_unit
(

   input  logic             clk_i,
   input  logic             rst_ni,
   input  logic             test_en_i,
   
   // EXTERNAL INITIATOR
   //***************************************
   output logic [3:0]       tcdm_req_o,
   output logic [3:0][31:0] tcdm_add_o,
   output logic [3:0]       tcdm_we_o,
   output logic [3:0][31:0] tcdm_wdata_o,
   output logic [3:0][3:0]  tcdm_be_o,
   input  logic [3:0]       tcdm_gnt_i,
   
   input  logic [3:0][31:0] tcdm_r_rdata_i,
   input  logic [3:0]       tcdm_r_valid_i,
   
   // RD CMD INTERFACE
   //***************************************
   input  logic [1:0][5:0]  trans_rd_id_i,
   input  logic [1:0][31:0] trans_rd_add_i,
   input  logic [1:0]       trans_rd_last_i,
   input  logic [1:0]       trans_rd_req_i,
   input  logic [1:0][3:0]  trans_rd_be_i,
   output logic [1:0]       trans_rd_gnt_o,
   
   // WR CMD INTERFACE
   //***************************************
   input  logic [1:0][5:0]  trans_wr_id_i,
   input  logic [1:0][31:0] trans_wr_add_i,
   input  logic [1:0]       trans_wr_last_i,
   input  logic [1:0]       trans_wr_req_i,
   output logic [1:0]       trans_wr_gnt_o,
   
   // WRITE SYNCHRONIZATION INTERFACE
   //***************************************
   input  logic             synch_wr_gnt_i,
   output logic             synch_wr_req_o,
   output logic [5:0]       synch_wr_id_o,
   
   // RD DATA INTERFACE
   //***************************************
   output logic [1:0][31:0] data_rd_dat_o,
   output logic [1:0]       data_rd_req_o,
   input  logic [1:0]       data_rd_gnt_i,
   output logic [5:0]       data_rd_id_o,
   output logic             data_rd_last_o,
   
   // WR DATA INTERFACE
   //***************************************
   input  logic [1:0][31:0] data_wr_dat_i,
   input  logic [1:0][3:0]  data_wr_strb_i,
   output logic [1:0]       data_wr_req_o,
   input  logic [1:0]       data_wr_gnt_i
);
   
   logic [1:0][31:0]        s_trans_rd_add,s_trans_wr_add;
   logic [1:0][3:0]         s_trans_rd_be;
   logic [1:0][5:0]         s_trans_rd_id,s_trans_wr_id;
   logic [1:0]              s_trans_rd_req,s_trans_wr_req;
   logic [1:0]              s_trans_rd_gnt,s_trans_wr_gnt;
   logic [1:0]              s_trans_rd_last,s_trans_wr_last;
   
   logic [1:0]              s_synch_wr_req;
   logic [1:0][5:0]         s_synch_wr_id;
   
   logic [1:0]              s_data_rd_last;
   logic [1:0][5:0]         s_data_rd_id;
   
   genvar            i;
   
   //**********************************************************
   //*************** TCDM TRANS QUEUE RD **********************
   //**********************************************************
   
   generate
      for (i=0; i<2; i++)
      begin : tcdm_rd_queue
         generic_fifo
         #(
            .DATA_WIDTH(39+4),
            .DATA_DEPTH(2)
         )
         tcdm_rd_queue_i
         (
            .clk          ( clk_i                                                    ),
            .rst_n        ( rst_ni                                                   ),
            .test_mode_i  ( test_en_i                                                ),

            .data_i       ( {trans_rd_be_i[i],trans_rd_id_i[i],trans_rd_last_i[i],trans_rd_add_i[i]}  ),
            .valid_i      ( trans_rd_req_i[i]                                        ),
            .grant_o      ( trans_rd_gnt_o[i]                                        ),

            .data_o       ( {s_trans_rd_be[i],s_trans_rd_id[i],s_trans_rd_last[i],s_trans_rd_add[i]}  ),
            .grant_i      ( s_trans_rd_gnt[i]                                        ),
            .valid_o      ( s_trans_rd_req[i]                                        )
         ); 
      end
   endgenerate




   
   //**********************************************************
   //*************** TCDM TRANS QUEUE WR **********************
   //**********************************************************
   
   generate
      
      for (i=0; i<2; i++)
      begin : tcdm_wr_queue
         generic_fifo
         #(
            .DATA_WIDTH(39),
            .DATA_DEPTH(2)
         )
         tcdm_wr_queue_i
         (
            .clk         ( clk_i                                                    ),
            .rst_n       ( rst_ni                                                   ),
            .test_mode_i ( test_en_i                                                ),

            .data_i      ( {trans_wr_id_i[i],trans_wr_last_i[i],trans_wr_add_i[i]}  ),
            .valid_i     ( trans_wr_req_i[i]                                        ),
            .grant_o     ( trans_wr_gnt_o[i]                                        ),

            .data_o      ( {s_trans_wr_id[i],s_trans_wr_last[i],s_trans_wr_add[i]}  ),
            .grant_i     ( s_trans_wr_gnt[i]                                        ),
            .valid_o     ( s_trans_wr_req[i]                                        )
         );     
      end
      
   endgenerate
   
   //**********************************************************
   //*************** TCDM INTERFACE RD ************************
   //**********************************************************
   
   generate
      
      for (i=0; i<2; i++)
        
        begin : tcdm_if_rd
           
           axi2mem_tcdm_rd_if tcdm_rd_if_i
           (
              .clk_i          ( clk_i              ),
              .rst_ni         ( rst_ni             ),
              .test_en_i      ( test_en_i          ),
              
              .trans_id_i     ( s_trans_rd_id  [i] ),
              .trans_last_i   ( s_trans_rd_last[i] ),
              .trans_add_i    ( s_trans_rd_add [i] ),
              .trans_be_i     ( s_trans_rd_be  [i] ),
              .trans_req_i    ( s_trans_rd_req [i] ),
              .trans_gnt_o    ( s_trans_rd_gnt [i] ),
              
              .data_dat_o     ( data_rd_dat_o  [i] ),
              .data_id_o      ( s_data_rd_id   [i] ),
              .data_last_o    ( s_data_rd_last [i] ),
              .data_req_o     ( data_rd_req_o  [i] ),
              .data_gnt_i     ( data_rd_gnt_i  [i] ),
              
              .tcdm_req_o     ( tcdm_req_o     [i] ),
              .tcdm_add_o     ( tcdm_add_o     [i] ),
              .tcdm_we_o      ( tcdm_we_o      [i] ),
              .tcdm_wdata_o   ( tcdm_wdata_o   [i] ),
              .tcdm_be_o      ( tcdm_be_o      [i] ),
              .tcdm_gnt_i     ( tcdm_gnt_i     [i] ),
              
              .tcdm_r_rdata_i ( tcdm_r_rdata_i [i] ),
              .tcdm_r_valid_i ( tcdm_r_valid_i [i] )
           );
           
        end
      
   endgenerate

   assign data_rd_id_o   = s_data_rd_id[0];
   assign data_rd_last_o = s_data_rd_last[0];
   
   //**********************************************************
   //*************** TCDM INTERFACE WR ************************
   //**********************************************************
   
   generate
      
      for (i=0; i<2; i++) 
      begin : tcdm_if_wr
           
           axi2mem_tcdm_wr_if tcdm_wr_if_i
           (
              .clk_i(clk_i),
              .rst_ni(rst_ni),
              
              .trans_id_i(s_trans_wr_id[i]),
              .trans_last_i(s_trans_wr_last[i]),
              .trans_add_i(s_trans_wr_add[i]),
              .trans_req_i(s_trans_wr_req[i]),
              .trans_gnt_o(s_trans_wr_gnt[i]),
              
              .synch_req_o(s_synch_wr_req[i]),
              .synch_id_o(s_synch_wr_id[i]),
              
              .data_dat_i(data_wr_dat_i[i]),
              .data_strb_i(data_wr_strb_i[i]),
              .data_req_o(data_wr_req_o[i]),
              .data_gnt_i(data_wr_gnt_i[i]),
              
              .tcdm_req_o(tcdm_req_o[i+2]),
              .tcdm_add_o(tcdm_add_o[i+2]),
              .tcdm_we_o(tcdm_we_o[i+2]),
              .tcdm_wdata_o(tcdm_wdata_o[i+2]),
              .tcdm_be_o(tcdm_be_o[i+2]),
              .tcdm_gnt_i(tcdm_gnt_i[i+2]),
              
              .tcdm_r_rdata_i(tcdm_r_rdata_i[i+2]),
              .tcdm_r_valid_i(tcdm_r_valid_i[i+2])
           );
      end
      
   endgenerate
   
   //**********************************************************
   //*************** TCDM SYNCH WR ****************************
   //**********************************************************
   
   axi2mem_tcdm_synch axi2mem_tcdm_synch_wr_i
   (
      .clk_i        ( clk_i           ),
      .rst_ni       ( rst_ni          ),
      .test_en_i    ( test_en_i       ),

      .synch_req_i  ( s_synch_wr_req  ),
      .synch_id_i   ( s_synch_wr_id   ),

      .synch_gnt_i  ( synch_wr_gnt_i  ),
      .synch_req_o  ( synch_wr_req_o  ),
      .synch_id_o   ( synch_wr_id_o   )
   );
   
endmodule
