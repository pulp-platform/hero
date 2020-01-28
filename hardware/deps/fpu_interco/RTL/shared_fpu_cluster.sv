////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// Copyright 2018 ETH Zurich and University of Bologna.                       //
// Copyright and related rights are licensed under the Solderpad Hardware     //
// License, Version 0.51 (the "License"); you may not use this file except in //
// compliance with the License.  You may obtain a copy of the License at      //
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law  //
// or agreed to in writing, software, hardware and materials distributed under//
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR     //
// CONDITIONS OF ANY KIND, either express or implied. See the License for the //
// specific language governing permissions and limitations under the License. //
//                                                                            //
// Company:        Micrel Lab @ DEIS - University of Bologna                  //
//                    Viale Risorgimento 2 40136                              //
//                    Bologna - fax 0512093785 -                              //
//                                                                            //
// Engineer:       Igor Loi - igor.loi@unibo.it                               //
//                                                                            //
// Additional contributions by:                                               //
//                                                                            //
//                                                                            //
//                                                                            //
// Create Date:    01/01/2019                                                 //
// Design Name:    FPU_INTERCONNECT                                           //
// Module Name:    shared_fpu_cluster                                         //
// Project Name:   VEGA                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    This Block represents the cluster of FP to be shared       //
//                 among the different cores. It includes The Demuxes         //
//                 to route FP request to the proper interco, the different   //
//                 interconnects, and the shared FP units                     //
//                                                                            //
//                                                                            //
// Revision:                                                                  //
// Revision v0.1 - 01/01/2019 : File Created                                  //
//                                                                            //
// Additional Comments:                                                       //
//                                                                            //
//                                                                            //
//                                                                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module shared_fpu_cluster
#(
   parameter NB_CORES         = 9, // 9 cores
   parameter NB_APUS          = 1, // 3 APUs
   parameter NB_FPNEW         = 4,

   parameter FP_TYPE_WIDTH     = 3, // From Wolf
   parameter NB_CORE_ARGS      = 3,

   parameter CORE_DATA_WIDTH   = 32,
   parameter CORE_OPCODE_WIDTH = 6,
   parameter CORE_DSFLAGS_CPU  = 15,
   parameter CORE_USFLAGS_CPU  = 5,

   parameter NB_APU_ARGS        = 2,
   parameter APU_OPCODE_WIDTH   = 6,
   parameter APU_DSFLAGS_CPU    = 15,
   parameter APU_USFLAGS_CPU    = 5,

   parameter NB_FPNEW_ARGS        = 3,
   parameter FPNEW_OPCODE_WIDTH   = 6,
   parameter FPNEW_DSFLAGS_CPU    = 15,
   parameter FPNEW_USFLAGS_CPU    = 5,

   parameter APUTYPE_ID       = 1, // ID is 5 in MrWolf
   parameter FPNEWTYPE_ID     = 0,

   parameter C_FPNEW_FMTBITS  = fpnew_pkg::FP_FORMAT_BITS,
   parameter C_FPNEW_IFMTBITS = fpnew_pkg::INT_FORMAT_BITS,
   parameter C_ROUND_BITS     = 3,
   parameter C_FPNEW_OPBITS   = fpnew_pkg::OP_BITS,

   parameter USE_FPU_OPT_ALLOC   = "FALSE", // IF NB_APUS  == 1 --> SET to FALSE
   parameter USE_FPNEW_OPT_ALLOC = "TRUE",  // IF NB_FPNEW == 1 --> SET to FALSE

   parameter FPNEW_INTECO_TYPE = "SINGLE_INTERCO" // CUSTOM | SINGLE_INTERCO
)
(
   input logic                                                        clk,
   input logic                                                        rst_n,
   input logic                                                        test_mode_i,

   // CORE SIDE: Slave port
   input  logic [NB_CORES-1:0]                                        core_slave_req_i,
   output logic [NB_CORES-1:0]                                        core_slave_gnt_o,
   input  logic [NB_CORES-1:0][FP_TYPE_WIDTH-1:0]                     core_slave_type_i,

   // request channel
   input logic [NB_CORES-1:0][NB_CORE_ARGS-1:0][CORE_DATA_WIDTH-1:0]  core_slave_operands_i,
   input logic [NB_CORES-1:0][CORE_OPCODE_WIDTH-1:0]                  core_slave_op_i,
   input logic [NB_CORES-1:0][CORE_DSFLAGS_CPU-1:0]                   core_slave_flags_i,

   // response channel
   input  logic [NB_CORES-1:0]                                        core_slave_rready_i,
   output logic [NB_CORES-1:0]                                        core_slave_rvalid_o,
   output logic [NB_CORES-1:0][CORE_DATA_WIDTH-1:0]                   core_slave_rdata_o,
   output logic [NB_CORES-1:0][CORE_USFLAGS_CPU-1:0]                  core_slave_rflags_o
);

   localparam APU_ID_WIDTH   = NB_CORES;
   localparam FPNEW_ID_WIDTH = NB_CORES;

   // APU Side: Master port
   logic [NB_CORES-1:0]                                          s_apu_master_req;
   logic [NB_CORES-1:0]                                          s_apu_master_gnt;

   // request channel
   logic [NB_CORES-1:0] [NB_APU_ARGS-1:0][CORE_DATA_WIDTH-1:0]   s_apu_master_operands;
   logic [NB_CORES-1:0] [APU_OPCODE_WIDTH-1:0]                   s_apu_master_op;
   logic [NB_CORES-1:0] [APU_DSFLAGS_CPU-1:0]                    s_apu_master_flags;

   // response channel
   logic [NB_CORES-1:0]                                          s_apu_master_rready;
   logic [NB_CORES-1:0]                                          s_apu_master_rvalid;
   logic [NB_CORES-1:0] [CORE_DATA_WIDTH-1:0]                    s_apu_master_rdata;
   logic [NB_CORES-1:0] [APU_USFLAGS_CPU-1:0]                    s_apu_master_rflags;


   // APU Side: Master port
   logic [NB_APUS-1:0]                                           s_apu_slave_req;
   logic [NB_APUS-1:0]                                           s_apu_slave_gnt;
   logic [NB_APUS-1:0][APU_ID_WIDTH-1:0]                         s_apu_slave_ID;

   // request channel
   logic [NB_APUS-1:0][NB_APU_ARGS-1:0][CORE_DATA_WIDTH-1:0]     s_apu_slave_operands;
   logic [NB_APUS-1:0][APU_OPCODE_WIDTH-1:0]                     s_apu_slave_op;
   logic [NB_APUS-1:0][APU_DSFLAGS_CPU-1:0]                      s_apu_slave_flags;

   // response channel
   logic [NB_APUS-1:0]                                           s_apu_slave_rready;
   logic [NB_APUS-1:0]                                           s_apu_slave_rvalid;
   logic [NB_APUS-1:0][CORE_DATA_WIDTH-1:0]                      s_apu_slave_rdata;
   logic [NB_APUS-1:0][APU_USFLAGS_CPU-1:0]                      s_apu_slave_rflags;
   logic [NB_APUS-1:0][APU_ID_WIDTH-1:0]                         s_apu_slave_rID;


   // FPNEW Side: Master port
   logic [NB_CORES-1:0]                                          s_fpnew_master_req;
   logic [NB_CORES-1:0]                                          s_fpnew_master_gnt;

   // request channel
   logic [NB_CORES-1:0] [NB_FPNEW_ARGS-1:0][CORE_DATA_WIDTH-1:0]  s_fpnew_master_operands;
   logic [NB_CORES-1:0] [FPNEW_OPCODE_WIDTH-1:0]                  s_fpnew_master_op;
   logic [NB_CORES-1:0] [FPNEW_DSFLAGS_CPU-1:0]                   s_fpnew_master_flags;

   // response channel
   logic [NB_CORES-1:0]                                          s_fpnew_master_rready;
   logic [NB_CORES-1:0]                                          s_fpnew_master_rvalid;
   logic [NB_CORES-1:0] [CORE_DATA_WIDTH-1:0]                    s_fpnew_master_rdata;
   logic [NB_CORES-1:0] [FPNEW_USFLAGS_CPU-1:0]                  s_fpnew_master_rflags;



   // FPNEW Side: Master port
   logic [NB_FPNEW-1:0]                                          s_fpnew_slave_req;
   logic [NB_FPNEW-1:0]                                          s_fpnew_slave_gnt;
   logic [NB_FPNEW-1:0][FPNEW_ID_WIDTH-1:0]                      s_fpnew_slave_ID;

   // request channel
   logic [NB_FPNEW-1:0][NB_FPNEW_ARGS-1:0][CORE_DATA_WIDTH-1:0]  s_fpnew_slave_operands;
   logic [NB_FPNEW-1:0][FPNEW_OPCODE_WIDTH-1:0]                  s_fpnew_slave_op;
   logic [NB_FPNEW-1:0][FPNEW_DSFLAGS_CPU-1:0]                   s_fpnew_slave_flags;

   // response channel
   logic [NB_FPNEW-1:0]                                          s_fpnew_slave_rready;
   logic [NB_FPNEW-1:0]                                          s_fpnew_slave_rvalid;
   logic [NB_FPNEW-1:0][CORE_DATA_WIDTH-1:0]                     s_fpnew_slave_rdata;
   logic [NB_FPNEW-1:0][FPNEW_USFLAGS_CPU-1:0]                   s_fpnew_slave_rflags;
   logic [NB_FPNEW-1:0][FPNEW_ID_WIDTH-1:0]                      s_fpnew_slave_rID;

   // signals used to clock gate the FPNEW/FPUs
   logic [NB_APUS-1:0]               s_fpu_clock_gate_enable;
   logic [NB_FPNEW-1:0]              s_fpnew_clock_gate_enable;

   logic [NB_APUS-1:0]               clk_fpu;
   logic [NB_FPNEW-1:0]              clk_fpnew;

  genvar i;
  generate
    for(i=0;i<NB_CORES;i++)
    begin : FPU_DEMUX
        fpu_demux
        #(
            .DATA_WIDTH          ( CORE_DATA_WIDTH    ),
            .FP_TYPE_WIDTH       ( FP_TYPE_WIDTH      ),  //= 5,
            .NB_CORE_ARGS        ( NB_CORE_ARGS       ),  //= 3,
            .CORE_OPCODE_WIDTH   ( CORE_OPCODE_WIDTH  ),  //= 6,
            .CORE_DSFLAGS_CPU    ( CORE_DSFLAGS_CPU   ),  //= 15,
            .CORE_USFLAGS_CPU    ( CORE_USFLAGS_CPU   ),  //= 5,

            .NB_APU_ARGS         ( NB_APU_ARGS        ),  //= 3,
            .APU_OPCODE_WIDTH    ( APU_OPCODE_WIDTH   ),  //= 6,
            .APU_DSFLAGS_CPU     ( APU_DSFLAGS_CPU    ),  //= 15,
            .APU_USFLAGS_CPU     ( APU_USFLAGS_CPU    ),  //= 5,

            .NB_FPNEW_ARGS       ( NB_FPNEW_ARGS      ),  //= 3,
            .FPNEW_OPCODE_WIDTH  ( FPNEW_OPCODE_WIDTH ),  //= 6,
            .FPNEW_DSFLAGS_CPU   ( FPNEW_DSFLAGS_CPU  ),  //= 15,
            .FPNEW_USFLAGS_CPU   ( FPNEW_USFLAGS_CPU  ),  //= 5,

            .APU_ID              ( APUTYPE_ID         ),  //= 1,
            .FPNEW_ID            ( FPNEWTYPE_ID       )   //= 0
        )
        i_fpu_demux
        (
           .clk                   ( clk   ),
           .rst_n                 ( rst_n ),

           // CORE SIDE: Slave port
           .core_slave_req_i      ( core_slave_req_i     [i] ),
           .core_slave_gnt_o      ( core_slave_gnt_o     [i] ),
           .core_slave_type_i     ( core_slave_type_i    [i] ),
           .core_slave_operands_i ( core_slave_operands_i[i] ),
           .core_slave_op_i       ( core_slave_op_i      [i] ),
           .core_slave_flags_i    ( core_slave_flags_i   [i] ),
           .core_slave_rready_i   ( core_slave_rready_i  [i] ),
           .core_slave_rvalid_o   ( core_slave_rvalid_o  [i] ),
           .core_slave_rdata_o    ( core_slave_rdata_o   [i] ),
           .core_slave_rflags_o   ( core_slave_rflags_o  [i] ),


           // APU Side: Master port
           .apu_req_o             (   s_apu_master_req       [i]    ),
           .apu_gnt_i             (   s_apu_master_gnt       [i]    ),

           // request channel
           .apu_operands_o        (   s_apu_master_operands  [i]    ),
           .apu_op_o              (   s_apu_master_op        [i]    ),
           .apu_flags_o           (   s_apu_master_flags     [i]    ),

           // response channel
           .apu_rready_o          (   s_apu_master_rready    [i]    ),
           .apu_rvalid_i          (   s_apu_master_rvalid    [i]    ),
           .apu_rdata_i           (   s_apu_master_rdata     [i]    ),
           .apu_rflags_i          (   s_apu_master_rflags    [i]    ),



           // FPNEW Side: Master port
           .fpnew_req_o           ( s_fpnew_master_req       [i]    ),
           .fpnew_gnt_i           ( s_fpnew_master_gnt       [i]    ),

           // request channel
           .fpnew_operands_o      ( s_fpnew_master_operands  [i]    ),
           .fpnew_op_o            ( s_fpnew_master_op        [i]    ),
           .fpnew_flags_o         ( s_fpnew_master_flags     [i]    ),

           // response channel
           .fpnew_rready_o        ( s_fpnew_master_rready    [i]    ),
           .fpnew_rvalid_i        ( s_fpnew_master_rvalid    [i]    ),
           .fpnew_rdata_i         ( s_fpnew_master_rdata     [i]    ),
           .fpnew_rflags_i        ( s_fpnew_master_rflags    [i]    )
        );
    end

  endgenerate



genvar k;
generate
    if(NB_APUS == NB_CORES)
    begin : PRIVATE_FPU
      for(k=0;k<NB_APUS;k++)
      begin
          assign s_apu_slave_req[k]      =  s_apu_master_req[k];
          assign s_apu_master_gnt[k]     =  s_apu_slave_gnt[k];
          assign s_apu_slave_ID[k]       =  '0;
          assign s_apu_slave_operands[k] =  s_apu_master_operands[k];
          assign s_apu_slave_op[k]       =  s_apu_master_op[k];
          assign s_apu_slave_flags[k]    =  s_apu_master_flags[k];
          assign s_apu_slave_rready[k]   =  s_apu_master_rready[k];
          assign s_apu_master_rvalid[k]  =  s_apu_slave_rvalid[k];
          assign s_apu_master_rdata[k]   =  s_apu_slave_rdata[k];
          assign s_apu_master_rflags[k]  =  s_apu_slave_rflags[k];
      end
    end
    else
    begin : SHARED_FPU
         XBAR_FPU
         #(
             .NB_CORES          ( NB_CORES          ), //= 8,
             .NB_APUS           ( NB_APUS           ), //= 1,
             .NB_APU_ARGS       ( NB_APU_ARGS       ), //= 2,
             .APU_DATA_WIDTH    ( CORE_DATA_WIDTH   ), //= 32,
             .APU_OPCODE_WIDTH  ( APU_OPCODE_WIDTH  ), //= 2,
             .APU_DSFLAGS_CPU   ( APU_DSFLAGS_CPU   ), //= 2,
             .APU_USFLAGS_CPU   ( APU_USFLAGS_CPU   ), //= 2,
             .ID_WIDTH          ( APU_ID_WIDTH      ),
             .USE_OPT_ALLOC     ( USE_FPU_OPT_ALLOC )
         )
         i_XBAR_APU
         (
             .clk                   ( clk                   ),
             .rst_n                 ( rst_n                 ),

             // CORE SIDE: Slave port
             .apu_slave_req_i       ( s_apu_master_req             ),
             .apu_slave_gnt_o       ( s_apu_master_gnt             ),
             .apu_slave_operands_i  ( s_apu_master_operands        ),
             .apu_slave_op_i        ( s_apu_master_op              ),
             .apu_slave_flags_i     ( s_apu_master_flags           ),
             .apu_slave_ready_i     ( s_apu_master_rready          ),
             .apu_slave_rvalid_o    ( s_apu_master_rvalid          ),
             .apu_slave_rdata_o     ( s_apu_master_rdata           ),
             .apu_slave_rflags_o    ( s_apu_master_rflags          ),


             // APU Side: Master port
             .apu_master_req_o      ( s_apu_slave_req             ),
             .apu_master_gnt_i      ( s_apu_slave_gnt             ),
             .apu_master_ID_o       ( s_apu_slave_ID              ),
             .apu_master_operands_o ( s_apu_slave_operands        ),
             .apu_master_op_o       ( s_apu_slave_op              ),
             .apu_master_flags_o    ( s_apu_slave_flags           ),
             .apu_master_ready_o    ( s_apu_slave_rready          ),
             .apu_master_rvalid_i   ( s_apu_slave_rvalid          ),
             .apu_master_rdata_i    ( s_apu_slave_rdata           ),
             .apu_master_rflags_i   ( s_apu_slave_rflags          ),
             .apu_master_rID_i      ( s_apu_slave_rID             )
         );
    end
endgenerate




generate
  if(NB_FPNEW == NB_CORES)
  begin : PRIVATE_FPNEW
      for(k=0;k<NB_FPNEW;k++)
      begin : FPNEW_BINDING
          assign s_fpnew_slave_req[k]      =  s_fpnew_master_req[k];
          assign s_fpnew_master_gnt[k]     =  s_fpnew_slave_gnt[k];
          assign s_fpnew_slave_ID[k]       =  '0;
          assign s_fpnew_slave_operands[k] =  s_fpnew_master_operands[k];
          assign s_fpnew_slave_op[k]       =  s_fpnew_master_op[k];
          assign s_fpnew_slave_flags[k]    =  s_fpnew_master_flags[k];
          assign s_fpnew_slave_rready[k]   =  s_fpnew_master_rready[k];
          assign s_fpnew_master_rvalid[k]  =  s_fpnew_slave_rvalid[k];
          assign s_fpnew_master_rdata[k]   =  s_fpnew_slave_rdata[k];
          assign s_fpnew_master_rflags[k]  =  s_fpnew_slave_rflags[k];
      end

  end
  else
  begin : SHARED_FPNEW
    if(FPNEW_INTECO_TYPE == "SINGLE_INTERCO")
    begin : SINGLE_INTERCO
         XBAR_FPU
         #(
             .NB_CORES          ( NB_CORES            ), //= 9,
             .NB_APUS           ( NB_FPNEW            ), //= 1,
             .NB_APU_ARGS       ( NB_FPNEW_ARGS       ), //= 2,
             .APU_DATA_WIDTH    ( CORE_DATA_WIDTH     ), //= 32,
             .APU_OPCODE_WIDTH  ( FPNEW_OPCODE_WIDTH  ), //= 2,
             .APU_DSFLAGS_CPU   ( FPNEW_DSFLAGS_CPU   ), //= 2,
             .APU_USFLAGS_CPU   ( FPNEW_USFLAGS_CPU   ),  //= 2,
             .ID_WIDTH          ( FPNEW_ID_WIDTH      ),
             .USE_OPT_ALLOC     ( USE_FPNEW_OPT_ALLOC )
         )
         i_XBAR_FPNEW
         (
             .clk                   ( clk                   ),
             .rst_n                 ( rst_n                 ),

             // CORE SIDE: Slave port
             .apu_slave_req_i       ( s_fpnew_master_req              ),
             .apu_slave_gnt_o       ( s_fpnew_master_gnt              ),
             .apu_slave_operands_i  ( s_fpnew_master_operands         ),
             .apu_slave_op_i        ( s_fpnew_master_op               ),
             .apu_slave_flags_i     ( s_fpnew_master_flags            ),
             .apu_slave_ready_i     ( s_fpnew_master_rready           ),
             .apu_slave_rvalid_o    ( s_fpnew_master_rvalid           ),
             .apu_slave_rdata_o     ( s_fpnew_master_rdata            ),
             .apu_slave_rflags_o    ( s_fpnew_master_rflags           ),


             // APU Side: Master port
             .apu_master_req_o      ( s_fpnew_slave_req               ),
             .apu_master_gnt_i      ( s_fpnew_slave_gnt               ),
             .apu_master_ID_o       ( s_fpnew_slave_ID                ),
             .apu_master_operands_o ( s_fpnew_slave_operands          ),
             .apu_master_op_o       ( s_fpnew_slave_op                ),
             .apu_master_flags_o    ( s_fpnew_slave_flags             ),
             .apu_master_ready_o    ( s_fpnew_slave_rready            ),
             .apu_master_rvalid_i   ( s_fpnew_slave_rvalid            ),
             .apu_master_rdata_i    ( s_fpnew_slave_rdata             ),
             .apu_master_rflags_i   ( s_fpnew_slave_rflags            ),
             .apu_master_rID_i      ( s_fpnew_slave_rID               )
         );
    end
    else
    begin : CUSTOM_INTERCO
           XBAR_FPU
           #(
               .NB_CORES          ( 2                  ), //= 9,
               .NB_APUS           ( 1                  ), //= 1,
               .NB_APU_ARGS       ( NB_FPNEW_ARGS      ), //= 2,
               .APU_DATA_WIDTH    ( CORE_DATA_WIDTH    ), //= 32,
               .APU_OPCODE_WIDTH  ( FPNEW_OPCODE_WIDTH ), //= 2,
               .APU_DSFLAGS_CPU   ( FPNEW_DSFLAGS_CPU  ), //= 2,
               .APU_USFLAGS_CPU   ( FPNEW_USFLAGS_CPU  ),  //= 2,
               .ID_WIDTH          ( FPNEW_ID_WIDTH     )
           )
           i_XBAR_FPNEW_0_4
           (
               .clk                   ( clk                   ),
               .rst_n                 ( rst_n                 ),

               // CORE SIDE: Slave port
               .apu_slave_req_i       ( {s_fpnew_master_req      [4], s_fpnew_master_req      [0]  }  ),
               .apu_slave_gnt_o       ( {s_fpnew_master_gnt      [4], s_fpnew_master_gnt      [0]  }  ),
               .apu_slave_operands_i  ( {s_fpnew_master_operands [4], s_fpnew_master_operands [0]  }  ),
               .apu_slave_op_i        ( {s_fpnew_master_op       [4], s_fpnew_master_op       [0]  }  ),
               .apu_slave_flags_i     ( {s_fpnew_master_flags    [4], s_fpnew_master_flags    [0]  }  ),
               .apu_slave_ready_i     ( {s_fpnew_master_rready   [4], s_fpnew_master_rready   [0]  }  ),
               .apu_slave_rvalid_o    ( {s_fpnew_master_rvalid   [4], s_fpnew_master_rvalid   [0]  }  ),
               .apu_slave_rdata_o     ( {s_fpnew_master_rdata    [4], s_fpnew_master_rdata    [0]  }  ),
               .apu_slave_rflags_o    ( {s_fpnew_master_rflags   [4], s_fpnew_master_rflags   [0]  }  ),


               // APU Side: Master port
               .apu_master_req_o      ( s_fpnew_slave_req      [0]      ),
               .apu_master_gnt_i      ( s_fpnew_slave_gnt      [0]      ),
               .apu_master_ID_o       ( s_fpnew_slave_ID       [0]      ),
               .apu_master_operands_o ( s_fpnew_slave_operands [0]      ),
               .apu_master_op_o       ( s_fpnew_slave_op       [0]      ),
               .apu_master_flags_o    ( s_fpnew_slave_flags    [0]      ),
               .apu_master_ready_o    ( s_fpnew_slave_rready   [0]      ),
               .apu_master_rvalid_i   ( s_fpnew_slave_rvalid   [0]      ),
               .apu_master_rdata_i    ( s_fpnew_slave_rdata    [0]      ),
               .apu_master_rflags_i   ( s_fpnew_slave_rflags   [0]      ),
               .apu_master_rID_i      ( s_fpnew_slave_rID      [0]      )
           );


           XBAR_FPU
           #(
               .NB_CORES          ( 2                  ), //= 9,
               .NB_APUS           ( 1                  ), //= 1,
               .NB_APU_ARGS       ( NB_FPNEW_ARGS      ), //= 2,
               .APU_DATA_WIDTH    ( CORE_DATA_WIDTH    ), //= 32,
               .APU_OPCODE_WIDTH  ( FPNEW_OPCODE_WIDTH ), //= 2,
               .APU_DSFLAGS_CPU   ( FPNEW_DSFLAGS_CPU  ), //= 2,
               .APU_USFLAGS_CPU   ( FPNEW_USFLAGS_CPU  ),  //= 2,
               .ID_WIDTH          ( FPNEW_ID_WIDTH     )
           )
           i_XBAR_FPNEW_1_5
           (
               .clk                   ( clk                   ),
               .rst_n                 ( rst_n                 ),

               // CORE SIDE: Slave port
               .apu_slave_req_i       ( {s_fpnew_master_req      [5], s_fpnew_master_req      [1]  }  ),
               .apu_slave_gnt_o       ( {s_fpnew_master_gnt      [5], s_fpnew_master_gnt      [1]  }  ),
               .apu_slave_operands_i  ( {s_fpnew_master_operands [5], s_fpnew_master_operands [1]  }  ),
               .apu_slave_op_i        ( {s_fpnew_master_op       [5], s_fpnew_master_op       [1]  }  ),
               .apu_slave_flags_i     ( {s_fpnew_master_flags    [5], s_fpnew_master_flags    [1]  }  ),
               .apu_slave_ready_i     ( {s_fpnew_master_rready   [5], s_fpnew_master_rready   [1]  }  ),
               .apu_slave_rvalid_o    ( {s_fpnew_master_rvalid   [5], s_fpnew_master_rvalid   [1]  }  ),
               .apu_slave_rdata_o     ( {s_fpnew_master_rdata    [5], s_fpnew_master_rdata    [1]  }  ),
               .apu_slave_rflags_o    ( {s_fpnew_master_rflags   [5], s_fpnew_master_rflags   [1]  }  ),


               // APU Side: Master port
               .apu_master_req_o      ( s_fpnew_slave_req      [1]     ),
               .apu_master_gnt_i      ( s_fpnew_slave_gnt      [1]     ),
               .apu_master_ID_o       ( s_fpnew_slave_ID       [1]     ),
               .apu_master_operands_o ( s_fpnew_slave_operands [1]     ),
               .apu_master_op_o       ( s_fpnew_slave_op       [1]     ),
               .apu_master_flags_o    ( s_fpnew_slave_flags    [1]     ),
               .apu_master_ready_o    ( s_fpnew_slave_rready   [1]     ),
               .apu_master_rvalid_i   ( s_fpnew_slave_rvalid   [1]     ),
               .apu_master_rdata_i    ( s_fpnew_slave_rdata    [1]     ),
               .apu_master_rflags_i   ( s_fpnew_slave_rflags   [1]     ),
               .apu_master_rID_i      ( s_fpnew_slave_rID      [1]     )
           );


           XBAR_FPU
           #(
               .NB_CORES          ( 2                  ), //= 9,
               .NB_APUS           ( 1                  ), //= 1,
               .NB_APU_ARGS       ( NB_FPNEW_ARGS      ), //= 2,
               .APU_DATA_WIDTH    ( CORE_DATA_WIDTH    ), //= 32,
               .APU_OPCODE_WIDTH  ( FPNEW_OPCODE_WIDTH ), //= 2,
               .APU_DSFLAGS_CPU   ( FPNEW_DSFLAGS_CPU  ), //= 2,
               .APU_USFLAGS_CPU   ( FPNEW_USFLAGS_CPU  ),  //= 2,
               .ID_WIDTH          ( FPNEW_ID_WIDTH     )
           )
           i_XBAR_FPNEW_2_6
           (
               .clk                   ( clk                   ),
               .rst_n                 ( rst_n                 ),

               // CORE SIDE: Slave port
               .apu_slave_req_i       ( {s_fpnew_master_req      [6], s_fpnew_master_req      [2]  }  ),
               .apu_slave_gnt_o       ( {s_fpnew_master_gnt      [6], s_fpnew_master_gnt      [2]  }  ),
               .apu_slave_operands_i  ( {s_fpnew_master_operands [6], s_fpnew_master_operands [2]  }  ),
               .apu_slave_op_i        ( {s_fpnew_master_op       [6], s_fpnew_master_op       [2]  }  ),
               .apu_slave_flags_i     ( {s_fpnew_master_flags    [6], s_fpnew_master_flags    [2]  }  ),
               .apu_slave_ready_i     ( {s_fpnew_master_rready   [6], s_fpnew_master_rready   [2]  }  ),
               .apu_slave_rvalid_o    ( {s_fpnew_master_rvalid   [6], s_fpnew_master_rvalid   [2]  }  ),
               .apu_slave_rdata_o     ( {s_fpnew_master_rdata    [6], s_fpnew_master_rdata    [2]  }  ),
               .apu_slave_rflags_o    ( {s_fpnew_master_rflags   [6], s_fpnew_master_rflags   [2]  }  ),


               // APU Side: Master port
               .apu_master_req_o      ( s_fpnew_slave_req      [2]     ),
               .apu_master_gnt_i      ( s_fpnew_slave_gnt      [2]     ),
               .apu_master_ID_o       ( s_fpnew_slave_ID       [2]     ),
               .apu_master_operands_o ( s_fpnew_slave_operands [2]     ),
               .apu_master_op_o       ( s_fpnew_slave_op       [2]     ),
               .apu_master_flags_o    ( s_fpnew_slave_flags    [2]     ),
               .apu_master_ready_o    ( s_fpnew_slave_rready   [2]     ),
               .apu_master_rvalid_i   ( s_fpnew_slave_rvalid   [2]     ),
               .apu_master_rdata_i    ( s_fpnew_slave_rdata    [2]     ),
               .apu_master_rflags_i   ( s_fpnew_slave_rflags   [2]     ),
               .apu_master_rID_i      ( s_fpnew_slave_rID      [2]     )
           );


           XBAR_FPU
           #(
               .NB_CORES          ( 3                  ), //= 9,
               .NB_APUS           ( 1                  ), //= 1,
               .NB_APU_ARGS       ( NB_FPNEW_ARGS      ), //= 2,
               .APU_DATA_WIDTH    ( CORE_DATA_WIDTH    ), //= 32,
               .APU_OPCODE_WIDTH  ( FPNEW_OPCODE_WIDTH ), //= 2,
               .APU_DSFLAGS_CPU   ( FPNEW_DSFLAGS_CPU  ), //= 2,
               .APU_USFLAGS_CPU   ( FPNEW_USFLAGS_CPU  ),  //= 2,
               .ID_WIDTH          ( FPNEW_ID_WIDTH     )
           )
           i_XBAR_FPNEW_3_7_8
           (
               .clk                   ( clk                   ),
               .rst_n                 ( rst_n                 ),

               // CORE SIDE: Slave port
               .apu_slave_req_i       ( { s_fpnew_master_req      [8:7], s_fpnew_master_req      [3]  }  ),
               .apu_slave_gnt_o       ( { s_fpnew_master_gnt      [8:7], s_fpnew_master_gnt      [3]  }  ),
               .apu_slave_operands_i  ( { s_fpnew_master_operands [8:7], s_fpnew_master_operands [3]  }  ),
               .apu_slave_op_i        ( { s_fpnew_master_op       [8:7], s_fpnew_master_op       [3]  }  ),
               .apu_slave_flags_i     ( { s_fpnew_master_flags    [8:7], s_fpnew_master_flags    [3]  }  ),
               .apu_slave_ready_i     ( { s_fpnew_master_rready   [8:7], s_fpnew_master_rready   [3]  }  ),
               .apu_slave_rvalid_o    ( { s_fpnew_master_rvalid   [8:7], s_fpnew_master_rvalid   [3]  }  ),
               .apu_slave_rdata_o     ( { s_fpnew_master_rdata    [8:7], s_fpnew_master_rdata    [3]  }  ),
               .apu_slave_rflags_o    ( { s_fpnew_master_rflags   [8:7], s_fpnew_master_rflags   [3]  }  ),


               // APU Side: Master port
               .apu_master_req_o      ( s_fpnew_slave_req      [3]     ),
               .apu_master_gnt_i      ( s_fpnew_slave_gnt      [3]     ),
               .apu_master_ID_o       ( s_fpnew_slave_ID       [3]     ),
               .apu_master_operands_o ( s_fpnew_slave_operands [3]     ),
               .apu_master_op_o       ( s_fpnew_slave_op       [3]     ),
               .apu_master_flags_o    ( s_fpnew_slave_flags    [3]     ),
               .apu_master_ready_o    ( s_fpnew_slave_rready   [3]     ),
               .apu_master_rvalid_i   ( s_fpnew_slave_rvalid   [3]     ),
               .apu_master_rdata_i    ( s_fpnew_slave_rdata    [3]     ),
               .apu_master_rflags_i   ( s_fpnew_slave_rflags   [3]     ),
               .apu_master_rID_i      ( s_fpnew_slave_rID      [3]     )
           );
    end

  end

endgenerate






   genvar j;
   generate


      for(j=0;j<NB_APUS;j++)
      begin : APU_UNIT
         fp_iter_divsqrt_msv_wrapper_2_STAGE   // USES ETH componente PIPE | FPU ETH  | PIPE | PIPE | --> OUt
         #(
           .ID_WIDTH        ( APU_ID_WIDTH     ),
           .NB_ARGS         ( NB_APU_ARGS      ),
           .OPCODE_WIDTH    ( APU_OPCODE_WIDTH ),
           .DATA_WIDTH      ( CORE_DATA_WIDTH  ),
           .FLAGS_IN_WIDTH  ( APU_DSFLAGS_CPU  ),
           .FLAGS_OUT_WIDTH ( APU_USFLAGS_CPU  )
         )
         i_fp_divsqrt_wrapper
         (
            // Clock and Reset
            .clk            ( clk_fpu[j]               ),
            .rst_n          ( rst_n                    ),

            // APU Side: Master port
            .apu_req_i      ( s_apu_slave_req      [j] ),
            .apu_gnt_o      ( s_apu_slave_gnt      [j] ),
            .apu_ID_i       ( s_apu_slave_ID       [j] ),

            // request channel
            .apu_operands_i ( s_apu_slave_operands [j] ),
            .apu_op_i       ( s_apu_slave_op       [j] ),
            .apu_flags_i    ( s_apu_slave_flags    [j] ),

            // response channel
            .apu_rready_i   ( s_apu_slave_rready   [j] ), // not used
            .apu_rvalid_o   ( s_apu_slave_rvalid   [j] ),
            .apu_rdata_o    ( s_apu_slave_rdata    [j] ),
            .apu_rflags_o   ( s_apu_slave_rflags   [j] ),
            .apu_rID_o      ( s_apu_slave_rID      [j] )
         );
      end



      for(j=0;j<NB_FPNEW;j++)
      begin : FPNEW_UNIT
         fpnew_wrapper
         #(
           .ID_WIDTH         ( FPNEW_ID_WIDTH      ),
           .NB_ARGS          ( NB_FPNEW_ARGS       ),
           .DATA_WIDTH       ( CORE_DATA_WIDTH     ),
           .OPCODE_WIDTH     ( FPNEW_OPCODE_WIDTH  ),
           .FLAGS_IN_WIDTH   ( FPNEW_DSFLAGS_CPU   ),
           .FLAGS_OUT_WIDTH  ( FPNEW_USFLAGS_CPU   ),
           .C_FPNEW_FMTBITS  ( C_FPNEW_FMTBITS     ),
           .C_FPNEW_IFMTBITS ( C_FPNEW_IFMTBITS    ),
           .C_ROUND_BITS     ( C_ROUND_BITS        ),
           .C_FPNEW_OPBITS   ( C_FPNEW_OPBITS      ),
           .FP_DIVSQRT       ( 0                   )
         )
         i_fpnew_wrapper
         (
            // Clock and Reset
            .clk            ( clk_fpnew[j]         ),
            .rst_n          ( rst_n                ),

            // APU Side: Master port
            .apu_req_i      ( s_fpnew_slave_req      [j] ),
            .apu_gnt_o      ( s_fpnew_slave_gnt      [j] ),
            .apu_ID_i       ( s_fpnew_slave_ID       [j] ),

            // request channel
            .apu_operands_i ( s_fpnew_slave_operands [j] ),
            .apu_op_i       ( s_fpnew_slave_op       [j] ),
            .apu_flags_i    ( s_fpnew_slave_flags    [j] ),

            // response channel
            .apu_rready_i   ( s_fpnew_slave_rready   [j] ), // not used
            .apu_rvalid_o   ( s_fpnew_slave_rvalid   [j] ),
            .apu_rdata_o    ( s_fpnew_slave_rdata    [j] ),
            .apu_rflags_o   ( s_fpnew_slave_rflags   [j] ),
            .apu_rID_o      ( s_fpnew_slave_rID      [j] )
         );
      end

   endgenerate




    FPU_clock_gating
    #(
       .NB_FPU   ( NB_APUS  ), //= 1,
       .NB_FPNEW ( NB_FPNEW )  //= 4
    )
    i_FPU_clock_gating
    (
       .clk                           ( clk                       ),
       .rst_n                         ( rst_n                     ),

       .automatic_clock_gate_enable_i ( 1'b1                      ),

       .fpu_req_in_i                  ( s_apu_slave_req           ),
       .fpu_gnt_out_i                 ( s_apu_slave_gnt           ),
       .fpu_rvalid_out_i              ( s_apu_slave_rvalid        ),

       .fpnew_req_in_i                ( s_fpnew_slave_req         ),
       .fpnew_gnt_out_i               ( s_fpnew_slave_gnt         ),
       .fpnew_rvalid_out_i            ( s_fpnew_slave_rvalid      ),

       .fpu_clock_gate_enable_o       ( s_fpu_clock_gate_enable   ),
       .fpnew_clock_gate_enable_o     ( s_fpnew_clock_gate_enable )
    );


generate

    for(j=0;j<NB_FPNEW;j++)
    begin : FPNEW_CG
         cluster_clock_gating fpnew_clock_gating
         (
            .clk_o     ( clk_fpnew[j]                 ),
            .clk_i     ( clk                          ),
            .en_i      ( s_fpnew_clock_gate_enable[j] ),
            .test_en_i ( test_mode_i                  )
         );
    end

    for(j=0;j<NB_APUS;j++)
    begin : FPU_CG
         cluster_clock_gating fpu_clock_gating
         (
            .clk_o     ( clk_fpu[j]                   ),
            .clk_i     ( clk                          ),
            .en_i      ( s_fpu_clock_gate_enable[j]   ),
            .test_en_i ( test_mode_i                  )
         );
    end

endgenerate



endmodule
