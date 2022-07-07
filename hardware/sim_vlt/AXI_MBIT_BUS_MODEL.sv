//----------------------------------------------------------
// Title : AXI_BUS_MODEL
// File : AXI_GEN.v
// Date of creation : Fri Jul 20 14:41:04 2012 - v1.0
// Made by jhyup.lee@samsung.com
//  - Support :
//            - AXI3 protocol
//  - Non-Support :
//            - Out-of-order test
//----------------------------------------------------------


module AXI_MBIT_BUS_MODEL #(
    parameter               DWIDTH      = 256   ,   // Data-Width::Only valid 128 or 256
    parameter               AWIDTH      = 32    ,   // Address-Width -- DO NOT CHANGE
    parameter               IDWIDTH     = 16    ,   // ID bit-Width
    parameter               ACAPA       = 128       // Acceptance Capability
) (

    input   bit                     ACLK        ,   // CLK for AXI
    input   bit                     ARESETn     ,   // RESET

    input   bit                     RD_BUS_HOLD ,   // BRS control for read channel
    input   bit                     WR_BUS_HOLD ,   // BRS control for write channel
    input   bit                     BR_BUS_HOLD ,   // BRS control for back-response channel

    // AXI Read Address Ch
    output  bit                     O_ARREADY   ,   // Read address read
    input   bit                     I_ARVALID   ,   // Read address valid
    input   bit     [IDWIDTH- 1:0]  I_ARID      ,   // Read address ID
    input   bit     [AWIDTH - 1:0]  I_ARADDR    ,   // Read address
    input   bit     [3:0]           I_ARLEN     ,   // Burst length
    input   bit     [1:0]           I_ARBURST   ,   // Burst type

    // AXI Read Data Ch
    input   bit                     I_RREADY    ,   // Read data ready
    output  bit                     O_RVALID    ,   // Read valid
    output  bit     [IDWIDTH- 1:0]  O_RID       ,   // Read data ID
    output  bit     [DWIDTH - 1:0]  O_RDATA     ,   // Read data from AXI
    output  bit                     O_RLAST     ,   // Last read transfer
    output  bit     [1:0]           O_RRESP     ,   // Read status response - always okay in here.

    // AXI Write Address Ch
    output  bit                     O_AWREADY   ,   // Write address read
    input   bit                     I_AWVALID   ,   // Write address valid
    input   bit     [IDWIDTH-1 :0]  I_AWID      ,   // Write address ID
    input   bit     [AWIDTH - 1:0]  I_AWADDR    ,   // Write address
    input   bit     [3:0]           I_AWLEN     ,   // Burst length
    input   bit     [1:0]           I_AWBURST   ,   // Burst type

    // AXI Write Data Ch
    output  bit                     O_WREADY    ,   // Write data ready
    input   bit                     I_WVALID    ,   // Write valid
    input   bit     [IDWIDTH-1 :0]  I_WID       ,   // Write data ID
    input   bit     [DWIDTH/8-1:0]  I_WSTRB     ,   // Write data strobe from AXI
    input   bit     [DWIDTH - 1:0]  I_WDATA     ,   // Write data from AXI
    input   bit                     I_WLAST     ,   // Last read transfer

    // AXI Response Ch
    input   bit                     I_BREADY    ,   // Write response READY
    output  bit                     O_BVALID    ,   // Write response Valid
    output  bit     [1:0]           O_BRESP     ,   // Write response status
    output  bit     [IDWIDTH-1:0]   O_BID           // Write response ID
);


    //----------------------------------------------------------
    // Declare local-parameters
    //----------------------------------------------------------
    localparam  FIXED_BURST = 2'b00;
    localparam  INCR_BURST  = 2'b01;
    localparam  WRAP_BURST  = 2'b10;
    localparam  ADDR_LSB    = $clog2(DWIDTH/8);
    localparam  INCR_STEP   = DWIDTH == 128 ? 4 : 8;
    //----------------------------------------------------------


    //----------------------------------------------------------
    // Declare signals
    //----------------------------------------------------------
    typedef struct packed {
        bit [        1:0]   AxBURST ;
        bit [AWIDTH -1:0]   AxADDR  ;
        bit [        3:0]   AxLEN   ;
        bit [IDWIDTH-1:0]   AxID    ;
    } MO_FIFO_t;

    bit     [31:0]                  MEMORY_0_               ;
    bit     [31:0]                  MEMORY_1_               ;
    bit     [31:0]                  MEMORY_2_               ;
    bit     [31:0]                  MEMORY_3_               ;
    bit     [31:0]                  MEMORY_4_               ;
    bit     [31:0]                  MEMORY_5_               ;
    bit     [31:0]                  MEMORY_6_               ;
    bit     [31:0]                  MEMORY_7_               ;
    int unsigned                    DRAM_MODEL[int unsigned]; 
    MO_FIFO_t   [ACAPA-1:0]         RD_MO_FIFO              ; // AXI ReadChannel's Multiple_Outstanding FIFO
    MO_FIFO_t   [ACAPA-1:0]         WR_MO_FIFO              ; // AXI WriteChannel's Multiple_Outstanding FIFO
    bit                             RD_FIFO_EMPTY           ;
    bit                             RD_FIFO_FULL            ;
    bit                             WR_FIFO_EMPTY           ;
    bit                             WR_FIFO_FULL            ;
    bit     [ACAPA-1:0]             RD_MO_CNT, WR_MO_CNT    ;
    bit     [$clog2(ACAPA):0]       rd_wptr, rd_rptr        ;
    bit     [$clog2(ACAPA):0]       wr_wptr, wr_rptr        ;
    bit     [$clog2(ACAPA):0]       br_wptr, br_rptr        ;
    bit     [31:0]                  MRADDR, MWADDR          ;

    bit     [ 3:0]                  RLEN, WLEN              ;
    bit     [AWIDTH-1:0]            RADDR, WADDR            ;
    bit     [IDWIDTH-1:0]           RID, AWID               ;
    bit     [ 1:0]                  RBURST, WBURST          ;
    bit     [ 7:0]                  rlen_cnt, wlen_cnt      ;
    bit     [31:0]                  incr_raddr, incr_waddr  ;
    bit     [ 3:0]                  wrap_raddr, wrap_waddr  ;
    //----------------------------------------------------------


    //----------------------------------------------------------
    // Read channel output
    //----------------------------------------------------------
    assign  O_ARREADY   = !RD_FIFO_FULL ;
    assign  O_RID       = RID       ;
    assign  O_RDATA     = DWIDTH == 128 ? {MEMORY_3_, MEMORY_2_, MEMORY_1_, MEMORY_0_} 
                          : {MEMORY_7_, MEMORY_6_, MEMORY_5_, MEMORY_4_, MEMORY_3_, MEMORY_2_, MEMORY_1_, MEMORY_0_};
    assign  O_RLAST     = O_RVALID && (RLEN == rlen_cnt) ;
    assign  O_RVALID    = |RD_MO_CNT && !RD_BUS_HOLD ;
    assign  O_RRESP     = 'h0       ; // TBD

    assign  MRADDR      = RBURST == INCR_BURST ? 32'({RADDR[31:ADDR_LSB  ],             ADDR_LSB'('h0)}/4) + incr_raddr
                                               : RBURST == WRAP_BURST ? 32'({RADDR[31:ADDR_LSB+4], wrap_raddr, ADDR_LSB'('h0)}/4)
                                               : 32'({RADDR[31:ADDR_LSB  ],             ADDR_LSB'('h0)}/4) ; // FIXED_BURST

    assign  MEMORY_0_   = DRAM_MODEL[MRADDR+0];
    assign  MEMORY_1_   = DRAM_MODEL[MRADDR+1];
    assign  MEMORY_2_   = DRAM_MODEL[MRADDR+2];
    assign  MEMORY_3_   = DRAM_MODEL[MRADDR+3];
    assign  MEMORY_4_   = DWIDTH == 128 ? '0 : DRAM_MODEL[MRADDR+4] ;
    assign  MEMORY_5_   = DWIDTH == 128 ? '0 : DRAM_MODEL[MRADDR+5] ;
    assign  MEMORY_6_   = DWIDTH == 128 ? '0 : DRAM_MODEL[MRADDR+6] ;
    assign  MEMORY_7_   = DWIDTH == 128 ? '0 : DRAM_MODEL[MRADDR+7] ;

    assign  RBURST      = O_RVALID ? RD_MO_FIFO[rd_rptr[$clog2(ACAPA)-1:0]].AxBURST : 'h0 ;
    assign  RADDR       = RD_MO_FIFO[rd_rptr[$clog2(ACAPA)-1:0]].AxADDR ;
    assign  RLEN        = RD_MO_FIFO[rd_rptr[$clog2(ACAPA)-1:0]].AxLEN  ;
    assign  RID         = RD_MO_FIFO[rd_rptr[$clog2(ACAPA)-1:0]].AxID   ;

    assign  wrap_raddr  = RLEN == 15 ?                        4'(RADDR[ADDR_LSB+:4] + rlen_cnt) 
                          : RLEN == 7  ? {RADDR[ADDR_LSB+3+:1], 3'(RADDR[ADDR_LSB+:3] + rlen_cnt)}
                          : RLEN == 3  ? {RADDR[ADDR_LSB+2+:2], 2'(RADDR[ADDR_LSB+:2] + rlen_cnt)}
                          : RLEN == 1  ? {RADDR[ADDR_LSB+1+:3], 1'(RADDR[ADDR_LSB+:1] + rlen_cnt)}
                                       :  RADDR[ADDR_LSB+0+:4];

    always_ff @(posedge ACLK or negedge ARESETn) begin
        if(!ARESETn) begin
            rlen_cnt        <= 'h0;
            incr_raddr      <= 'h0;
        end
        else if(I_RREADY && O_RVALID && O_RLAST) begin
            rlen_cnt        <= 'h0;
            incr_raddr      <= 'h0;
        end
        else if(I_RREADY && O_RVALID) begin
            rlen_cnt        <= rlen_cnt   + 'h1;
            incr_raddr      <= incr_raddr + INCR_STEP;
        end
    end
    //----------------------------------------------------------


    //----------------------------------------------------------
    // Write channel output
    //----------------------------------------------------------
    assign  O_AWREADY   = !WR_FIFO_FULL ;
    assign  O_WREADY    = !WR_BUS_HOLD  ;

    assign  MWADDR      = ({WADDR[31:ADDR_LSB],ADDR_LSB'('h0)}/4 + incr_waddr);
    assign  WADDR       = WR_MO_FIFO[wr_rptr[$clog2(ACAPA)-1:0]].AxADDR ;
    assign  WBURST      = WR_MO_FIFO[wr_rptr[$clog2(ACAPA)-1:0]].AxBURST;
    assign  AWID        = WR_MO_FIFO[wr_rptr[$clog2(ACAPA)-1:0]].AxID   ;

    always_ff @(posedge ACLK) begin
        if(O_WREADY && I_WVALID) begin
            if(I_WSTRB[ 0]) DRAM_MODEL[MWADDR  ][(8*0)+:8] <= I_WDATA[(8* 0)+:8] ;
            if(I_WSTRB[ 1]) DRAM_MODEL[MWADDR  ][(8*1)+:8] <= I_WDATA[(8* 1)+:8] ;
            if(I_WSTRB[ 2]) DRAM_MODEL[MWADDR  ][(8*2)+:8] <= I_WDATA[(8* 2)+:8] ;
            if(I_WSTRB[ 3]) DRAM_MODEL[MWADDR  ][(8*3)+:8] <= I_WDATA[(8* 3)+:8] ;
            if(I_WSTRB[ 4]) DRAM_MODEL[MWADDR+1][(8*0)+:8] <= I_WDATA[(8* 4)+:8] ;
            if(I_WSTRB[ 5]) DRAM_MODEL[MWADDR+1][(8*1)+:8] <= I_WDATA[(8* 5)+:8] ;
            if(I_WSTRB[ 6]) DRAM_MODEL[MWADDR+1][(8*2)+:8] <= I_WDATA[(8* 6)+:8] ;
            if(I_WSTRB[ 7]) DRAM_MODEL[MWADDR+1][(8*3)+:8] <= I_WDATA[(8* 7)+:8] ;
            if(I_WSTRB[ 7]) DRAM_MODEL[MWADDR+1][(8*3)+:8] <= I_WDATA[(8* 8)+:8] ;
            if(I_WSTRB[ 9]) DRAM_MODEL[MWADDR+2][(8*1)+:8] <= I_WDATA[(8* 9)+:8] ;
            if(I_WSTRB[10]) DRAM_MODEL[MWADDR+2][(8*2)+:8] <= I_WDATA[(8*10)+:8] ;
            if(I_WSTRB[11]) DRAM_MODEL[MWADDR+2][(8*3)+:8] <= I_WDATA[(8*11)+:8] ;
            if(I_WSTRB[12]) DRAM_MODEL[MWADDR+3][(8*0)+:8] <= I_WDATA[(8*12)+:8] ;
            if(I_WSTRB[13]) DRAM_MODEL[MWADDR+3][(8*1)+:8] <= I_WDATA[(8*13)+:8] ;
            if(I_WSTRB[14]) DRAM_MODEL[MWADDR+3][(8*2)+:8] <= I_WDATA[(8*14)+:8] ;
            if(I_WSTRB[15]) DRAM_MODEL[MWADDR+3][(8*3)+:8] <= I_WDATA[(8*15)+:8] ;
        end
    end

    generate if(DWIDTH != 128) begin:GEN_AXI256
        always_ff @(posedge ACLK) begin
            if(O_WREADY && I_WVALID) begin
                if(I_WSTRB[16+ 0]) DRAM_MODEL[4+MWADDR  ][(8*0)+:8] <= I_WDATA[128+(8* 0)+:8] ;
                if(I_WSTRB[16+ 1]) DRAM_MODEL[4+MWADDR  ][(8*1)+:8] <= I_WDATA[128+(8* 1)+:8] ;
                if(I_WSTRB[16+ 2]) DRAM_MODEL[4+MWADDR  ][(8*2)+:8] <= I_WDATA[128+(8* 2)+:8] ;
                if(I_WSTRB[16+ 3]) DRAM_MODEL[4+MWADDR  ][(8*3)+:8] <= I_WDATA[128+(8* 3)+:8] ;
                if(I_WSTRB[16+ 4]) DRAM_MODEL[4+MWADDR+1][(8*0)+:8] <= I_WDATA[128+(8* 4)+:8] ;
                if(I_WSTRB[16+ 5]) DRAM_MODEL[4+MWADDR+1][(8*1)+:8] <= I_WDATA[128+(8* 5)+:8] ;
                if(I_WSTRB[16+ 5]) DRAM_MODEL[4+MWADDR+1][(8*1)+:8] <= I_WDATA[128+(8* 6)+:8] ;
                if(I_WSTRB[16+ 5]) DRAM_MODEL[4+MWADDR+1][(8*1)+:8] <= I_WDATA[128+(8* 7)+:8] ;
                if(I_WSTRB[16+ 5]) DRAM_MODEL[4+MWADDR+1][(8*1)+:8] <= I_WDATA[128+(8* 8)+:8] ;
                if(I_WSTRB[16+ 9]) DRAM_MODEL[4+MWADDR+2][(8*1)+:8] <= I_WDATA[128+(8* 9)+:8] ;
                if(I_WSTRB[16+10]) DRAM_MODEL[4+MWADDR+2][(8*2)+:8] <= I_WDATA[128+(8*10)+:8] ;
                if(I_WSTRB[16+11]) DRAM_MODEL[4+MWADDR+2][(8*3)+:8] <= I_WDATA[128+(8*11)+:8] ;
                if(I_WSTRB[16+12]) DRAM_MODEL[4+MWADDR+3][(8*0)+:8] <= I_WDATA[128+(8*12)+:8] ;
                if(I_WSTRB[16+13]) DRAM_MODEL[4+MWADDR+3][(8*1)+:8] <= I_WDATA[128+(8*13)+:8] ;
                if(I_WSTRB[16+14]) DRAM_MODEL[4+MWADDR+3][(8*2)+:8] <= I_WDATA[128+(8*14)+:8] ;
                if(I_WSTRB[16+15]) DRAM_MODEL[4+MWADDR+3][(8*3)+:8] <= I_WDATA[128+(8*15)+:8] ;
            end
        end
    end
    endgenerate

    always_ff @(posedge ACLK or negedge ARESETn) begin
        if(!ARESETn) begin
            incr_waddr      <= 'h0;
        end
        else if(O_WREADY && I_WVALID && I_WLAST) begin
            incr_waddr      <= 'h0 ;
        end
        else if(O_WREADY && I_WVALID) begin
            incr_waddr      <= incr_waddr + INCR_STEP;
        end
    end
    //----------------------------------------------------------


    //----------------------------------------------------------
    // Back-Response channel output
    //----------------------------------------------------------
    assign  O_BVALID    = BR_BUS_HOLD ? 0 : br_wptr != br_rptr ;
    assign  O_BID       = WR_MO_FIFO[br_rptr[$clog2(ACAPA)-1:0]].AxID;
    assign  O_BRESP     = 'h0; // always return OKAY-response
    //----------------------------------------------------------


    //----------------------------------------------------------
    // RD MO FIFO
    //----------------------------------------------------------
    assign  RD_FIFO_EMPTY  = (rd_wptr == rd_rptr);
    assign  RD_FIFO_FULL   = (rd_wptr[$clog2(ACAPA)] != rd_rptr[$clog2(ACAPA)]) & (rd_wptr[$clog2(ACAPA)-1:0] == rd_rptr[$clog2(ACAPA)-1:0]);
    assign  RD_MO_CNT      = (rd_wptr[$clog2(ACAPA)] == rd_rptr[$clog2(ACAPA)]) ? {1'b0,rd_wptr[$clog2(ACAPA)-1:0]} - {1'b0,rd_rptr[$clog2(ACAPA)-1:0]}
                                                                                  : {1'b1,rd_wptr[$clog2(ACAPA)-1:0]} - {1'b0,rd_rptr[$clog2(ACAPA)-1:0]};
    // FIFO Write
    always_ff @(posedge ACLK or negedge ARESETn) begin
        if (I_ARVALID & O_ARREADY) begin
            RD_MO_FIFO[rd_wptr[$clog2(ACAPA)-1:0]].AxBURST  <= I_ARBURST[0+:2]     ;
            RD_MO_FIFO[rd_wptr[$clog2(ACAPA)-1:0]].AxADDR   <= I_ARADDR[0+:AWIDTH] ;
            RD_MO_FIFO[rd_wptr[$clog2(ACAPA)-1:0]].AxLEN    <= I_ARLEN[0+:4]       ;
            RD_MO_FIFO[rd_wptr[$clog2(ACAPA)-1:0]].AxID     <= I_ARID[0+:IDWIDTH]  ;
        end
    end

    // FIFO Write Pointer
    always_ff @(posedge ACLK or negedge ARESETn) begin
        if(!ARESETn) begin
            rd_wptr   <= 'h0;
        end
        else if(I_ARVALID & O_ARREADY) begin
            rd_wptr   <= rd_wptr + 'h1;
        end
    end

    // FIFO Read Pointer
    always_ff @(posedge ACLK or negedge ARESETn) begin
        if(!ARESETn) begin
            rd_rptr <= 'h0;
        end
        else if(I_RREADY && O_RVALID && O_RLAST) begin
            rd_rptr <= rd_rptr + 'h1;
        end
    end
    //----------------------------------------------------------



    //----------------------------------------------------------
    // WR MO FIFO
    //----------------------------------------------------------
    assign  WR_FIFO_EMPTY  = (wr_wptr == br_rptr);
    assign  WR_FIFO_FULL   = (wr_wptr[$clog2(ACAPA)] != br_rptr[$clog2(ACAPA)]) & (wr_wptr[$clog2(ACAPA)-1:0] == br_rptr[$clog2(ACAPA)-1:0]);
    assign  WR_MO_CNT      = (wr_wptr[$clog2(ACAPA)] == br_rptr[$clog2(ACAPA)]) ? {1'b0,wr_wptr[$clog2(ACAPA)-1:0]} - {1'b0,br_rptr[$clog2(ACAPA)-1:0]}
                                                                                  : {1'b1,wr_wptr[$clog2(ACAPA)-1:0]} - {1'b0,br_rptr[$clog2(ACAPA)-1:0]};

    // FIFO Write
    always_ff @(posedge ACLK or negedge ARESETn) begin
        if (I_AWVALID & O_AWREADY) begin
            WR_MO_FIFO[wr_wptr[$clog2(ACAPA)-1:0]].AxBURST  <= I_AWBURST[0+:2]      ;
            WR_MO_FIFO[wr_wptr[$clog2(ACAPA)-1:0]].AxADDR   <= I_AWADDR[0+:AWIDTH]  ;
            WR_MO_FIFO[wr_wptr[$clog2(ACAPA)-1:0]].AxLEN    <= I_AWLEN[0+:4]        ;
            WR_MO_FIFO[wr_wptr[$clog2(ACAPA)-1:0]].AxID     <= I_AWID[0+:IDWIDTH]   ;
        end
    end

    // FIFO Write Pointer for WR-channel
    always_ff @(posedge ACLK or negedge ARESETn) begin
        if(!ARESETn) begin
            wr_wptr   <= 'h0;
        end
        else if(I_AWVALID & O_AWREADY) begin
            wr_wptr   <= wr_wptr + 'h1;
        end
    end

    // FIFO Read Pointer for WR-channel
    always_ff @(posedge ACLK or negedge ARESETn) begin
        if(!ARESETn) begin
            wr_rptr <= 'h0;
        end
        else if(I_WVALID && O_WREADY && I_WLAST) begin
            wr_rptr <= wr_rptr + 'h1;
        end
    end

    // FIFO Write Pointer for BR-channel
    assign  br_wptr = wr_rptr;

    // FIFO Read Pointer for BR-channel
    always_ff @(posedge ACLK or negedge ARESETn) begin
        if(!ARESETn) begin
            br_rptr <= 'h0;
        end
        else if(O_BVALID && I_BREADY) begin
            br_rptr <= br_rptr + 'h1;
        end
    end
    //----------------------------------------------------------


    //----------------------------------------------------------
    // TASK :: DRAM pre-load hex-text data
    //----------------------------------------------------------
    task PRELOAD;
        input   [31:0]  ADDR;
        input   string  FNAME;
        begin
            $display("memory preload -- %s @ 0x%0x", FNAME, ADDR);
            $readmemh(FNAME, DRAM_MODEL, ADDR[31:2]) ;
        end
    endtask:PRELOAD
    //----------------------------------------------------------


    //----------------------------------------------------------
    // TASK :: DRAM pre-load binary data
    //----------------------------------------------------------
    task BIN_PRELOAD;
        input   [31:0]  ADDR;
        input   string  FNAME;
        begin
            integer ifile, code ;
            integer ofile       ;
            bit [31:0]  word    ;
            string hex_FNAME    ;

            hex_FNAME   = {FNAME,".hex"};
            ifile = $fopen(FNAME, "rb");
            ofile = $fopen(hex_FNAME, "w");
            while($fread(word, ifile)) begin
                word = {<<8{word}};
                $fwrite(ofile, "%x\n", word);
            end
            $fclose(ifile);
            $fclose(ofile);

            PRELOAD(
                .ADDR       (ADDR       ),
                .FNAME      (hex_FNAME  )
            );
        end
    endtask:BIN_PRELOAD
    //----------------------------------------------------------


    //----------------------------------------------------------
    // TASK :: DRAM data file write
    //----------------------------------------------------------
    task DUMP;
        input   [31:0]  ADDR;
        input   string  FNAME;
        input   [31:0]  SIZE; // Byte
        begin
            integer ofile       ;

            if(SIZE) begin
                $display("dram dump -- 0x%0x, 0x%x Byte to %s", ADDR, SIZE, FNAME);
                ofile = $fopen(FNAME, "w");
                for(int i = 0; i < (SIZE/4 + |(SIZE%4)); i++) begin
                    $fwrite(ofile, "%x\n", DRAM_MODEL[(ADDR)/4+i]);
                end
                $fclose(ofile);
            end
            else begin
                $display("no dump %s since too small size(size should be positive integer)", FNAME);
            end
        end
    endtask:DUMP
    //----------------------------------------------------------


    //----------------------------------------------------------
    // TASK :: DRAM data file write
    //----------------------------------------------------------
    task BIN_DUMP;
        input   [31:0]  ADDR;
        input   string  FNAME;
        input   [31:0]  SIZE; // Byte
        begin
            integer ofile       ;
            bit [ 7:0] data     ;

            if(SIZE) begin
                $display("dram dump -- 0x%0x, 0x%x Byte to %s", ADDR, SIZE, FNAME);
                ofile = $fopen(FNAME, "wb");
                for(int i = 0; i < SIZE; i++) begin
                    data = DRAM_MODEL[(ADDR+i)/4][(i%4)*8+:8];
                    $fwriteb(ofile, "%c", data);
                end
                $fclose(ofile);
            end
            else begin
                $display("no dump %s since too small size(size should be positive integer)", FNAME);
            end
        end
    endtask:BIN_DUMP
    //----------------------------------------------------------



endmodule

