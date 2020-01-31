/*
 * Copyright (C) 2013-2017 ETH Zurich, University of Bologna
 * All rights reserved.
 *
 * This code is under development and not yet released to the public.
 * Until it is released, the code is under the copyright of ETH Zurich and
 * the University of Bologna, and may contain confidential and/or unpublished
 * work. Any reuse/redistribution is strictly forbidden without written
 * permission from ETH Zurich.
 *
 * Bug fixes and contributions will eventually be released under the
 * SolderPad open hardware license in the context of the PULP platform
 * (http://www.pulp-platform.org), under the copyright of ETH Zurich and the
 * University of Bologna.
 */


module l1_tcdm_bank_1024_32
(
    input  logic        CLK,
    input  logic        CEN,
    input  logic        WEN,
    input  logic [31:0] BW,
    input  logic [9:0]  A,
    input  logic [31:0] D,
    output logic [31:0] Q

  );

IN22FDX_S1D_NFRG_W01024B032M04C128 i_tcdm_bank
  (
        .CLK          ( CLK              ), 
        .CEN          ( CEN              ), 
        .RDWEN        ( WEN              ), 
        .AS           ( A[9]             ), 
        .AW           ( A[8:2]           ), 
        .AC           ( A[1:0]           ), 
        .D            ( D                ), 
        .BW           ( BW               ), 
        .Q            ( Q                ),
        .DEEPSLEEP    ( 1'b0             ), 
        .POWERGATE    ( 1'b0             ), 
        .T_BIST       ( 1'b0             ), 
        .T_LOGIC      ( 1'b0             ), 
        .T_CEN        ( 1'b1             ), 
        .T_RDWEN      ( 1'b1             ), 
        .T_DEEPSLEEP  ( 1'b0             ), 
        .T_POWERGATE  ( 1'b0             ), 
        .T_AS         ( '0               ), 
        .T_AW         ( '0               ), 
        .T_AC         ( '0               ), 
        .T_D          ( '0               ), 
        .T_BW         ( '0               ), 
        .T_WBT        ( '0               ), 
        .T_STAB       ( '0               ), 
        .MA_SAWL      ( '0               ), 
        .MA_WL        ( '0               ), 
        .MA_WRAS      ( '0               ), 
        .MA_WRASD     ( '0               ), 
        .OBSV_CTL     (                  )
    );
endmodule

module l1_tcdm_bank_1024_32_hp
(
    input  logic        CLK,
    input  logic        CEN,
    input  logic        WEN,
    input  logic [31:0] BW,
    input  logic [9:0]  A,
    input  logic [31:0] D,
    output logic [31:0] Q

  );

IN22FDX_R1PH_NFHN_W01024B032M04C256 i_tcdm_bank
  (
        .CLK          ( CLK              ), 
        .CEN          ( CEN              ), 
        .RDWEN        ( WEN              ), 
        .AW           ( A[9:2]           ), 
        .AC           ( A[1:0]           ), 
        .D            ( D                ), 
        .BW           ( BW               ), 
        .Q            ( Q                ),
        .T_LOGIC      ( 1'b0             ), 
        .MA_SAWL      ( '0               ), 
        .MA_WL        ( '0               ), 
        .MA_WRAS      ( '0               ), 
        .MA_WRASD     ( '0               ), 
        .OBSV_CTL     (                  )
    );

endmodule

module l2_mem_bank_32768x32
(
    input  logic        CLK,
    input  logic        RSTN,

    input  logic        CEN,
    input  logic        WEN,
    input  logic  [3:0] BEN,
    input  logic [14:0] A,
    input  logic [31:0] D,
    output logic [31:0] Q
);
         logic [7:0]       CEN_int;
         logic [7:0][31:0] Q_int;

         logic [2:0] muxsel;

         logic [31:0] BE_BW;

         logic [3:0]   BE;
         assign BE = ~BEN;

         assign BE_BW      = { {8{BE[3]}}, {8{BE[2]}}, {8{BE[1]}}, {8{BE[0]}} };



         assign CEN_int[0] = CEN |  A[14] |  A[13] |  A[12];
         assign CEN_int[1] = CEN |  A[14] |  A[13] | ~A[12];
         assign CEN_int[2] = CEN |  A[14] | ~A[13] |  A[12];
         assign CEN_int[3] = CEN |  A[14] | ~A[13] | ~A[12];
         assign CEN_int[4] = CEN | ~A[14] |  A[13] |  A[12];
         assign CEN_int[5] = CEN | ~A[14] |  A[13] | ~A[12];
         assign CEN_int[6] = CEN | ~A[14] | ~A[13] |  A[12];
         assign CEN_int[7] = CEN | ~A[14] | ~A[13] | ~A[12];


         assign Q = Q_int[muxsel];


         always_ff @(posedge CLK or negedge RSTN)
         begin
            if(~RSTN)
            begin
                muxsel <= '0;
            end
            else
            begin
                if(CEN == 1'b0)
                     muxsel <= A[14:12];
            end
         end

            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_0
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[0]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[0]         ), // output
              .OBSV_CTL     (                  )  // output
            );

            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_1
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[1]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[1]         ), // output
              .OBSV_CTL     (                  )  // output
            );

            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_2
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[2]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[2]         ), // output
              .OBSV_CTL     (                  )  // output
            );

            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_3
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[3]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[3]         ), // output
              .OBSV_CTL     (                  )  // output
            );

            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_4
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[4]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[4]         ), // output
              .OBSV_CTL     (                  )  // output
            );

            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_5
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[5]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[5]         ), // output
              .OBSV_CTL     (                  )  // output
            );

            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_6
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[6]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[6]         ), // output
              .OBSV_CTL     (                  )  // output
            );

            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_7
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[7]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[7]         ), // output
              .OBSV_CTL     (                  )  // output
            );

endmodule


module l2_mem_bank_28672x32
(
    input  logic        CLK,
    input  logic        RSTN,

    input  logic        CEN,
    input  logic        WEN,
    input  logic  [3:0] BEN,
    input  logic [14:0] A,
    input  logic [31:0] D,
    output logic [31:0] Q
);
         logic [6:0]       CEN_int;
         logic [6:0][31:0] Q_int;

         logic  [2:0] muxsel;
         logic [31:0] BE_BW;

         logic [3:0]   BE;
         assign BE = ~BEN;

         assign BE_BW      = { {8{BE[3]}}, {8{BE[2]}}, {8{BE[1]}}, {8{BE[0]}} };


         assign CEN_int[0] = CEN |  A[14] |  A[13] |  A[12];
         assign CEN_int[1] = CEN |  A[14] |  A[13] | ~A[12];
         assign CEN_int[2] = CEN |  A[14] | ~A[13] |  A[12];
         assign CEN_int[3] = CEN |  A[14] | ~A[13] | ~A[12];
         assign CEN_int[4] = CEN | ~A[14] |  A[13] |  A[12];
         assign CEN_int[5] = CEN | ~A[14] |  A[13] | ~A[12];
         assign CEN_int[6] = CEN | ~A[14] | ~A[13] |  A[12];


         assign Q = Q_int[muxsel];


         always_ff @(posedge CLK or negedge RSTN)
         begin
            if(~RSTN)
            begin
                muxsel <= '0;
            end
            else
            begin
                if(CEN == 1'b0)
                     muxsel <= A[14:12];
            end
         end


            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_0
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[0]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[0]         ), // output
              .OBSV_CTL     (                  )  // output
            );


            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_1
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[1]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[1]         ), // output
              .OBSV_CTL     (                  )  // output
            );


            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_2
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[2]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[2]         ), // output
              .OBSV_CTL     (                  )  // output
            );


            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_3
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[3]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[3]         ), // output
              .OBSV_CTL     (                  )  // output
            );



            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_4
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[4]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[4]         ), // output
              .OBSV_CTL     (                  )  // output
            );


            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_5
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[5]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[5]         ), // output
              .OBSV_CTL     (                  )  // output
            );


            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_6
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[6]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[6]         ), // output
              .OBSV_CTL     (                  )  // output
            );
endmodule





//********************************************************
//************* L2 RAM MEMORY WRAPPER ********************
//********************************************************
module l2_mem_bank_16384x32
(
    input  logic        CLK,
    input  logic        RSTN,

    input  logic        CEN,
    input  logic        WEN,
    input  logic  [3:0] BEN,
    input  logic [13:0] A,
    input  logic [31:0] D,
    output logic [31:0] Q
);
         logic [3:0]       CEN_int;
         logic [3:0][31:0] Q_int;

         logic [1:0] muxsel;
         logic [31:0] BE_BW;

         logic [3:0]   BE;
         assign BE = ~BEN;

         assign BE_BW      = { {8{BE[3]}}, {8{BE[2]}}, {8{BE[1]}}, {8{BE[0]}} };


         assign CEN_int[0] = CEN |  A[13] |  A[12];
         assign CEN_int[1] = CEN |  A[13] | ~A[12];
         assign CEN_int[2] = CEN | ~A[13] |  A[12];
         assign CEN_int[3] = CEN | ~A[13] | ~A[12];

         always @(*)
         begin
            case(muxsel)
               2'b00: Q=Q_int[0];
               2'b01: Q=Q_int[1];
               2'b10: Q=Q_int[2];
               2'b11: Q=Q_int[3];
            endcase
         end

         always_ff @(posedge CLK or negedge RSTN)
         begin
            if(~RSTN)
            begin
                muxsel <= '0;
            end
            else
            begin
                if(CEN == 1'b0)
                     muxsel <= A[13:12];
            end
         end


            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_0
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[0]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[0]         ), // output
              .OBSV_CTL     (                  )  // output
            );

            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_1
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[1]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[1]         ), // output
              .OBSV_CTL     (                  )  // output
            );



            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_2
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[2]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[2]         ), // output
              .OBSV_CTL     (                  )  // output
            );


            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_3
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[3]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[3]         ), // output
              .OBSV_CTL     (                  )  // output
            );

endmodule




//********************************************************
//************* L2 RAM MEMORY WRAPPER ********************
//********************************************************
module l2_mem_bank_12288x32
(
    input  logic        CLK,
    input  logic        RSTN,

    input  logic        CEN,
    input  logic        WEN,
    input  logic  [3:0] BEN,
    input  logic [13:0] A,
    input  logic [31:0] D,
    output logic [31:0] Q
);
         logic [3:0]       CEN_int;
         logic [3:0][31:0] Q_int;

         logic [1:0] muxsel;
         logic [31:0] BE_BW;

         logic [3:0]   BE;
         assign BE = ~BEN;

         assign BE_BW      = { {8{BE[3]}}, {8{BE[2]}}, {8{BE[1]}}, {8{BE[0]}} };


         assign CEN_int[0] = CEN |  A[13] |  A[12];
         assign CEN_int[1] = CEN |  A[13] | ~A[12];
         assign CEN_int[2] = CEN | ~A[13] |  A[12];
         assign CEN_int[3] = CEN | ~A[13] | ~A[12];

         always @(*)
         begin
            case(muxsel)
               2'b00: Q=Q_int[0];
               2'b01: Q=Q_int[1];
               2'b10: Q=Q_int[2];
               2'b11: Q=Q_int[3];
            endcase
         end

         always_ff @(posedge CLK or negedge RSTN)
         begin
            if(~RSTN)
            begin
                muxsel <= '0;
            end
            else
            begin
                if(CEN == 1'b0)
                     muxsel <= A[13:12];
            end
         end

            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_0
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[0]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[0]         ), // output
              .OBSV_CTL     (                  )  // output
            );

            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_1
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[1]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[1]         ), // output
              .OBSV_CTL     (                  )  // output
            );



            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_2
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[2]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[2]         ), // output
              .OBSV_CTL     (                  )  // output
            );
endmodule







//********************************************************
//************* L2 RAM MEMORY WRAPPER ********************
//********************************************************
module l2_mem_bank_8192x32
(
    input  logic        CLK,
    input  logic        RSTN,

    input  logic        CEN,
    input  logic        WEN,
    input  logic  [3:0] BEN,
    input  logic [12:0] A,
    input  logic [31:0] D,
    output logic [31:0] Q
);
         logic CEN_int[1:0];
         logic [1:0][31:0] Q_int;

         logic muxsel;
         logic [31:0] BE_BW;

         logic [3:0]   BE;
         assign BE = ~BEN;

         assign BE_BW      = { {8{BE[3]}}, {8{BE[2]}}, {8{BE[1]}}, {8{BE[0]}} };

         assign CEN_int[0] = CEN |   A[12];
         assign CEN_int[1] = CEN |  ~A[12];

         always @(*)
         begin
            case(muxsel)
               1'b0: Q=Q_int[0];
               1'b1: Q=Q_int[1];
            endcase
         end

         always_ff @(posedge CLK or negedge RSTN)
         begin
            if(~RSTN)
            begin
                muxsel <= '0;
            end
            else
            begin
                if(CEN == 1'b0)
                     muxsel <= A[12];
            end
         end


            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_0
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[0]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[0]         ), // output
              .OBSV_CTL     (                  )  // output
            );


            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_1
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[1]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[1]         ), // output
              .OBSV_CTL     (                  )  // output
            );

endmodule

module l2_mem_bank_4096x32
(
    input  logic        CLK,
    input  logic        RSTN,

    input  logic        CEN,
    input  logic        WEN,
    input  logic  [3:0] BEN,
    input  logic [11:0] A,
    input  logic [31:0] D,
    output logic [31:0] Q
);
         logic CEN_int;
         logic [31:0] Q_int;

         logic [31:0] BE_BW;

         logic [3:0]   BE;
         assign BE = ~BEN;

         assign BE_BW      = { {8{BE[3]}}, {8{BE[2]}}, {8{BE[1]}}, {8{BE[0]}} };

         assign CEN_int    = CEN;

            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_0
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int         ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int            ), // output
              .OBSV_CTL     (                  )  // output
            );

endmodule

module l2_mem_bank_6144x32_2048x32scm
(
    input  logic        CLK,
    input  logic        RSTN,

    input  logic        CEN,
    input  logic        CEN_scm0,
    input  logic        CEN_scm1,

    input  logic        WEN,
    input  logic        WEN_scm0,
    input  logic        WEN_scm1,

    input  logic  [3:0] BEN,
    input  logic  [3:0] BEN_scm0,

    input  logic [12:0] A,
    input  logic [10:0] A_scm0,
    input  logic [10:0] A_scm1,

    input  logic [31:0] D,
    input  logic [31:0] D_scm0,

    output logic [31:0] Q,
    output logic [31:0] Q_scm0,
    output logic [31:0] Q_scm1
);
         logic CEN_int[2:0];
         logic [2:0][31:0] Q_int;

         logic [1:0]  muxsel;
         logic [31:0] BE_BW;

         logic [3:0]   BE;
         logic [3:0]   BE_scm0;
         logic read_enA,read_enB,read_enC;
         logic write_enA,write_enB;


         assign BE      = ~BEN;
         assign BE_scm0 = ~BEN_scm0;

         assign BE_BW      = { {8{BE[3]}}, {8{BE[2]}}, {8{BE[1]}}, {8{BE[0]}} };

         assign CEN_int[2] = CEN |   ~A[12] | ~A[11]; //scm
         assign CEN_int[1] = CEN |   ~A[12] | A[11];
         assign CEN_int[0] = CEN |   A[12];

         always @(*)
         begin
            case(muxsel)
               2'b00: Q=Q_int[0];
               2'b01: Q=Q_int[0];
               2'b10: Q=Q_int[1];
               2'b11: Q=Q_int[2];
            endcase
         end

         always_ff @(posedge CLK or negedge RSTN)
         begin
            if(~RSTN)
            begin
                muxsel <= '0;
            end
            else
            begin
                if(CEN == 1'b0)
                     muxsel <= A[12:11];
            end
         end

            scm_2048x32 scm_0
            (
                .CLK       ( CLK          ),
                .RSTN      ( RSTN         ),
                .CEN       ( CEN_int[2]   ),
                .CEN_scm0  ( CEN_scm0     ),
                .CEN_scm1  ( CEN_scm1     ),

                .WEN       ( WEN          ),
                .WEN_scm0  ( WEN_scm0     ),
                .WEN_scm1  ( WEN_scm1     ),

                .BE        ( BE           ),
                .BE_scm0   ( BE_scm0      ),

                .A         ( A[10:0]      ),
                .A_scm0    ( A_scm0[10:0] ),
                .A_scm1    ( A_scm1[10:0] ),

                .D         ( D[31:0]      ),
                .D_scm0    ( D_scm0[31:0] ),

                .Q         ( Q_int[2]     ),
                .Q_scm0    ( Q_scm0       ),
                .Q_scm1    ( Q_scm1       )
            );

            IN22FDX_S1D_NFRG_W02048B032M04C128  cut_1
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[1]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[5:4]           ), // input
              .AW           ( {A[10:6],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[1]         ), // output
              .OBSV_CTL     (                  )  // output
            );

            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_0
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[0]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[0]         ), // output
              .OBSV_CTL     (                  )  // output
            );

endmodule

module l2_mem_bank_sram_28672x32_scm_512x32
(
    input  logic        CLK,
    input  logic        RSTN,

    input  logic        CEN,
    input  logic        WEN,
    input  logic  [3:0] BEN,
    input  logic [14:0] A,
    input  logic [31:0] D,
    output logic [31:0] Q
);
         logic [7:0]       CEN_int;
         logic [7:0][31:0] Q_int;

         logic  [2:0] muxsel;
         logic [31:0] BE_BW;

         logic [3:0]   BE;
         assign BE = ~BEN;

         assign BE_BW      = { {8{BE[3]}}, {8{BE[2]}}, {8{BE[1]}}, {8{BE[0]}} };


         assign CEN_int[0] = CEN |  A[14] |  A[13] |  A[12];
         assign CEN_int[1] = CEN |  A[14] |  A[13] | ~A[12];
         assign CEN_int[2] = CEN |  A[14] | ~A[13] |  A[12];
         assign CEN_int[3] = CEN |  A[14] | ~A[13] | ~A[12];
         assign CEN_int[4] = CEN | ~A[14] |  A[13] |  A[12];
         assign CEN_int[5] = CEN | ~A[14] |  A[13] | ~A[12];
         assign CEN_int[6] = CEN | ~A[14] | ~A[13] |  A[12];
         assign CEN_int[7] = CEN | ~A[14] | ~A[13] | ~A[12]; // 2KB scm

         assign Q = Q_int[muxsel];

         always_ff @(posedge CLK or negedge RSTN)
         begin
            if(~RSTN)
            begin
                muxsel <= '0;
            end
            else
            begin
                if(CEN == 1'b0)
                     muxsel <= A[14:12];
            end
         end

            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_0
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[0]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[0]         ), // output
              .OBSV_CTL     (                  )  // output
            );


            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_1
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[1]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[1]         ), // output
              .OBSV_CTL     (                  )  // output
            );


            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_2
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[2]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[2]         ), // output
              .OBSV_CTL     (                  )  // output
            );


            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_3
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[3]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[3]         ), // output
              .OBSV_CTL     (                  )  // output
            );



            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_4
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[4]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[4]         ), // output
              .OBSV_CTL     (                  )  // output
            );


            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_5
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[5]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[5]         ), // output
              .OBSV_CTL     (                  )  // output
            );


            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_6
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[6]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[6]         ), // output
              .OBSV_CTL     (                  )  // output
            );

            scm_512x32 scm_7
            (
              .CLK       ( CLK          ),
              .RSTN      ( RSTN         ),
              .CEN       ( CEN_int[7]   ),
              .WEN       ( WEN          ),
              .BE        ( BE           ),
              .A         ( A[ 8:0]      ), // 2 kB -> 9 bits; 4 kB -> 10 bits; 8 kB -> 11 bits; 16 kB -> 12 bits
              .D         ( D[31:0]      ),
              .Q         ( Q_int[7]     )
            );

endmodule

module l2_mem_bank_sram_28672x32_scm_1024x32
(
    input  logic        CLK,
    input  logic        RSTN,

    input  logic        CEN,
    input  logic        WEN,
    input  logic  [3:0] BEN,
    input  logic [14:0] A,
    input  logic [31:0] D,
    output logic [31:0] Q
);
         logic [7:0]       CEN_int;
         logic [7:0][31:0] Q_int;

         logic  [2:0] muxsel;
         logic [31:0] BE_BW;

         logic [3:0]   BE;
         assign BE = ~BEN;

         assign BE_BW      = { {8{BE[3]}}, {8{BE[2]}}, {8{BE[1]}}, {8{BE[0]}} };


         assign CEN_int[0] = CEN |  A[14] |  A[13] |  A[12];
         assign CEN_int[1] = CEN |  A[14] |  A[13] | ~A[12];
         assign CEN_int[2] = CEN |  A[14] | ~A[13] |  A[12];
         assign CEN_int[3] = CEN |  A[14] | ~A[13] | ~A[12];
         assign CEN_int[4] = CEN | ~A[14] |  A[13] |  A[12];
         assign CEN_int[5] = CEN | ~A[14] |  A[13] | ~A[12];
         assign CEN_int[6] = CEN | ~A[14] | ~A[13] |  A[12];
         assign CEN_int[7] = CEN | ~A[14] | ~A[13] | ~A[12]; // 4KB scm

         assign Q = Q_int[muxsel];

         always_ff @(posedge CLK or negedge RSTN)
         begin
            if(~RSTN)
            begin
                muxsel <= '0;
            end
            else
            begin
                if(CEN == 1'b0)
                     muxsel <= A[14:12];
            end
         end

            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_0
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[0]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[0]         ), // output
              .OBSV_CTL     (                  )  // output
            );


            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_1
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[1]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[1]         ), // output
              .OBSV_CTL     (                  )  // output
            );


            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_2
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[2]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[2]         ), // output
              .OBSV_CTL     (                  )  // output
            );


            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_3
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[3]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[3]         ), // output
              .OBSV_CTL     (                  )  // output
            );



            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_4
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[4]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[4]         ), // output
              .OBSV_CTL     (                  )  // output
            );


            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_5
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[5]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[5]         ), // output
              .OBSV_CTL     (                  )  // output
            );


            IN22FDX_S1D_NFRG_W04096B032M04C128  cut_6
            (
              .CLK          (  CLK             ), // input
              .CEN          (  CEN_int[6]      ), // input
              .RDWEN        ( WEN              ), // input
              .DEEPSLEEP    ( 1'b0             ), // input
              .POWERGATE    ( 1'b0             ), // input
              .AS           ( A[6:4]           ), // input
              .AW           ( {A[11:7],A[3:2]} ), // input
              .AC           ( A[1:0]           ), // input
              .D            ( D                ), // input
              .BW           ( BE_BW            ), // input
              .T_BIST       ( 1'b0             ), // input
              .T_LOGIC      ( 1'b0             ), // input
              .T_CEN        ( 1'b1             ), // input
              .T_RDWEN      ( 1'b1             ), // input
              .T_DEEPSLEEP  ( 1'b0             ), // input
              .T_POWERGATE  ( 1'b0             ), // input
              .T_AS         ( '0               ), // input
              .T_AW         ( '0               ), // input
              .T_AC         ( '0               ), // input
              .T_D          ( '0               ), // input
              .T_BW         ( '0               ), // input
              .T_WBT        ( 1'b0             ), // input
              .T_STAB       ( 1'b0             ), // input
              .MA_SAWL      ( '0               ), // input
              .MA_WL        ( '0               ), // input
              .MA_WRAS      ( '0               ), // input
              .MA_WRASD     ( 1'b0             ), // input
              .Q            ( Q_int[6]         ), // output
              .OBSV_CTL     (                  )  // output
            );

            scm_1024x32 scm_7
            (
              .CLK       ( CLK          ),
              .RSTN      ( RSTN         ),
              .CEN       ( CEN_int[7]   ),
              .WEN       ( WEN          ),
              .BE        ( BE           ),
              .A         ( A[ 9:0]      ), // 2 kB -> 9 bits; 4 kB -> 10 bits; 8 kB -> 11 bits; 16 kB -> 12 bits
              .D         ( D[31:0]      ),
              .Q         ( Q_int[7]     )
            );

endmodule
