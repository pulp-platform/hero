// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.


`define REG_INFO        7'b0000000 //BASEADDR+0x00 CONTAINS NUMBER OF CORES [31:16] AND CLUSTERS [15:0]
`define REG_FCBOOT      7'b0000001 //BASEADDR+0x04 not used at the moment
`define REG_FCFETCH     7'b0000010 //BASEADDR+0x08 not used at the moment

`define REG_PADFUN0     7'b0000100 //BASEADDR+0x10 sets the mux for pins  0 (bits [1:0]) to 15 (bits [31:30])
`define REG_PADFUN1     7'b0000101 //BASEADDR+0x14 sets the mux for pins 16 (bits [1:0]) to 31 (bits [31:30])
`define REG_PADFUN2     7'b0000110 //BASEADDR+0x18 sets the mux for pins 32 (bits [1:0]) to 47 (bits [31:30])
`define REG_PADFUN3     7'b0000111 //BASEADDR+0x1C sets the mux for pins 48 (bits [1:0]) to 63 (bits [31:30])

//PADs configuration is made of 8bits out of which only the first 6 are used
//bit0    enable pull UP
//bit1    enable pull DOWN
//bit2    enable ST
//bit3    enable SlewRate Limit
//bit4..5 Driving Strength
//bit6..7 not used
`define REG_PADCFG0     7'b0001000 //BASEADDR+0x20 sets config for pin  0(bits [7:0]) to pin  3(bits [31:24])
`define REG_PADCFG1     7'b0001001 //BASEADDR+0x24 sets config for pin  4(bits [7:0]) to pin  7(bits [31:24])
`define REG_PADCFG2     7'b0001010 //BASEADDR+0x28 sets config for pin  8(bits [7:0]) to pin 11(bits [31:24])
`define REG_PADCFG3     7'b0001011 //BASEADDR+0x2C sets config for pin 12(bits [7:0]) to pin 15(bits [31:24])
`define REG_PADCFG4     7'b0001100 //BASEADDR+0x30 sets config for pin 16(bits [7:0]) to pin 19(bits [31:24])
`define REG_PADCFG5     7'b0001101 //BASEADDR+0x34 sets config for pin 20(bits [7:0]) to pin 23(bits [31:24])
`define REG_PADCFG6     7'b0001110 //BASEADDR+0x38 sets config for pin 24(bits [7:0]) to pin 27(bits [31:24])
`define REG_PADCFG7     7'b0001111 //BASEADDR+0x3C sets config for pin 28(bits [7:0]) to pin 31(bits [31:24])
`define REG_PADCFG8     7'b0010000 //BASEADDR+0x40 sets config for pin 32(bits [7:0]) to pin 35(bits [31:24])
`define REG_PADCFG9     7'b0010001 //BASEADDR+0x44 sets config for pin 36(bits [7:0]) to pin 39(bits [31:24])
`define REG_PADCFG10    7'b0010010 //BASEADDR+0x48 sets config for pin 40(bits [7:0]) to pin 43(bits [31:24])
`define REG_PADCFG11    7'b0010011 //BASEADDR+0x4C sets config for pin 44(bits [7:0]) to pin 47(bits [31:24])
`define REG_PADCFG12    7'b0010100 //BASEADDR+0x50 sets config for pin 48(bits [7:0]) to pin 51(bits [31:24])
`define REG_PADCFG13    7'b0010101 //BASEADDR+0x54 sets config for pin 52(bits [7:0]) to pin 55(bits [31:24])
`define REG_PADCFG14    7'b0010110 //BASEADDR+0x58 sets config for pin 56(bits [7:0]) to pin 59(bits [31:24])
`define REG_PADCFG15    7'b0010111 //BASEADDR+0x5C sets config for pin 60(bits [7:0]) to pin 63(bits [31:24])

`define REG_JTAGREG     7'b0011101 //BASEADDR+0x74 JTAG REG

`define REG_CORESTATUS  7'b0101000 //BASEADDR+0xA0 32bit GP register to be used during testing to return EOC(bit[31]) and status(bit[30:0])
`define REG_CS_RO       7'b0110000 //BASEADDR+0xC0 32bit GP register to be used during testing to return EOC(bit[31]) and status(bit[30:0]) Read Only mirror
`define REG_BOOTSEL     7'b0110001 //BASEADDR+0xC4 bootsel
`define REG_CLKSEL      7'b0110010 //BASEADDR+0xC8 clocksel

`define REG_CLUSTER_CTRL 7'b0011100 //BASEADDR+0x70 CLUSTER Ctrl
`define REG_CTRL_PER     7'b0011110
`define REG_CLUSTER_IRQ  7'b0011111

`define REG_CLUSTER_BOOT_ADDR0 7'b0100000
`define REG_CLUSTER_BOOT_ADDR1 7'b0100001
// NOTE: safe regs will be mapped starting from BASEADDR+0x100

//`define MSG_VERBOSE

module apb_soc_ctrl
  #(
    parameter APB_ADDR_WIDTH = 12,  // APB slaves are 4KB by default
    parameter NB_CLUSTERS    = 0,   // N_CLUSTERS
    parameter NB_CORES       = 4,   // N_CORES
    parameter JTAG_REG_SIZE  = 8
    )
   (
    input  logic                      HCLK,
    input  logic                      HRESETn,
    input  logic [APB_ADDR_WIDTH-1:0] PADDR,
    input  logic               [31:0] PWDATA,
    input  logic                      PWRITE,
    input  logic                      PSEL,
    input  logic                      PENABLE,
    output logic               [31:0] PRDATA,
    output logic                      PREADY,
    output logic                      PSLVERR,

    input  logic                      sel_fll_clk_i,
    input  logic                      boot_l2_i,
    input  logic                      bootsel_i,

    output logic         [63:0] [3:0] pad_cfg,
    output logic         [63:0] [1:0] pad_mux,

    input  logic                [JTAG_REG_SIZE-1:0] soc_jtag_reg_i,
    output logic                [JTAG_REG_SIZE-1:0] soc_jtag_reg_o,

    output logic               [31:0] fc_bootaddr_o,

    output logic                      fc_fetchen_o,
    output logic                      sel_hyper_axi_o,
    output logic                      cluster_pow_o, // power cluster
    output logic                      cluster_byp_o, // bypass cluster
    output logic               [63:0] cluster_boot_addr_o,
    output logic                      cluster_fetch_enable_o,
    output logic                      cluster_rstn_o,
    output logic                      cluster_irq_o
    );

   logic     [31:0] r_pwr_reg;
   logic     [31:0] r_corestatus;


   logic      [6:0] s_apb_addr;

   logic     [15:0] n_cores;
   logic     [15:0] n_clusters;

   logic     [63:0] r_pad_fun0;
   logic     [63:0] r_pad_fun1;

   logic     [63:0] r_cluster_boot;
   logic            r_cluster_fetch_enable;
   logic            r_cluster_rstn;

   logic      [JTAG_REG_SIZE-1:0] r_jtag_rego;
   logic      [JTAG_REG_SIZE-1:0] r_jtag_regi_sync[1:0];

   logic            r_cluster_byp;
   logic            r_cluster_pow;
   logic     [31:0] r_bootaddr;
   logic            r_fetchen;

   logic            r_cluster_irq;

   logic            r_sel_hyper_axi;
   logic      [1:0] r_bootsel;

   logic s_apb_write;

   assign soc_jtag_reg_o = r_jtag_rego;

   assign fc_bootaddr_o = r_bootaddr;
   assign fc_fetchen_o  = r_fetchen;

   assign cluster_pow_o = r_cluster_pow;
   assign sel_hyper_axi_o = r_sel_hyper_axi;

   assign s_apb_write = PSEL && PENABLE && PWRITE;

   assign cluster_rstn_o = r_cluster_rstn;

   assign cluster_boot_addr_o = r_cluster_boot;
   assign cluster_fetch_enable_o = r_cluster_fetch_enable;
   assign cluster_byp_o = r_cluster_byp;
   assign cluster_irq_o = r_cluster_irq;

   always_comb begin
     for (int i=0;i<64;i++)
     begin
       pad_mux[i][0]  = r_pad_fun0[i];
       pad_mux[i][1]  = r_pad_fun1[i];
     end
   end


   assign s_apb_addr = PADDR[8:2];

    always_ff @(posedge HCLK, negedge HRESETn)
    begin
      if(~HRESETn) begin
        r_corestatus           <= '0;
        r_pwr_reg              <= '0;
        r_pad_fun0             <= '0;
        r_pad_fun1             <= '0;
        r_jtag_regi_sync[0]    <= 'h0;
        r_jtag_regi_sync[1]    <= 'h0;
        r_jtag_rego            <= 'h0;
        r_bootaddr             <= 32'h1A000080;
        r_fetchen              <= 'h1;
        r_cluster_pow          <= 1'b0;
        r_cluster_byp          <= 1'b1;
        pad_cfg                <= '{default: 4'b1111};
        r_sel_hyper_axi        <= 1'b0;
        r_cluster_fetch_enable <= 1'b0;
        r_cluster_boot         <= '0;
        r_cluster_rstn         <= 1'b1;
        r_cluster_irq          <= 1'b0;
      end
      else
      begin
        r_jtag_regi_sync[1] <= soc_jtag_reg_i;
        r_jtag_regi_sync[0] <= r_jtag_regi_sync[1];
        if (PSEL && PENABLE && PWRITE)
        begin
          case (s_apb_addr)
                `REG_FCBOOT:
                 begin
                   r_bootaddr <= PWDATA;
                 end
                `REG_FCFETCH:
                 begin
                   r_fetchen <= PWDATA[0];
                 end
                `REG_PADFUN0:
                for (int i=0;i<16;i++)
                begin
                  r_pad_fun0[i] <= PWDATA[i*2];
                  r_pad_fun1[i] <= PWDATA[i*2+1];
                end
               `REG_PADFUN1:
                for (int i=0;i<16;i++)
                begin
                  r_pad_fun0[16+i] <= PWDATA[i*2];
                  r_pad_fun1[16+i] <= PWDATA[i*2+1];
                end
                `REG_PADFUN2:
                for (int i=0;i<16;i++)
                begin
                  r_pad_fun0[32+i] <= PWDATA[i*2];
                  r_pad_fun1[32+i] <= PWDATA[i*2+1];
                end
                `REG_PADFUN3:
                for (int i=0;i<16;i++)
                begin
                  r_pad_fun0[48+i] <= PWDATA[i*2];
                  r_pad_fun1[48+i] <= PWDATA[i*2+1];
                end
                `REG_PADCFG0:
                begin
                  pad_cfg[0]         <= PWDATA[5:0];   //pad_rf_miso
                  pad_cfg[1]         <= PWDATA[13:8];  //pad_rf_mosi
                  pad_cfg[2]         <= PWDATA[21:16]; //pad_rf_cs
                  pad_cfg[3]         <= PWDATA[29:24]; //pad_rf_sck
                end
                `REG_PADCFG1:
                begin
                  pad_cfg[4]         <= PWDATA[5:0];   //pad_rf_pactrl0
                  pad_cfg[5]         <= PWDATA[13:8];  //pad_rf_pactrl1
                  pad_cfg[6]         <= PWDATA[21:16]; //pad_rf_pactrl2
                  pad_cfg[7]         <= PWDATA[29:24]; //pad_rf_pactrl3
                end
                `REG_PADCFG2:
                begin
                  pad_cfg[8]         <= PWDATA[5:0];   //pad_cam_pclk
                  pad_cfg[9]         <= PWDATA[13:8];  //pad_cam_valid
                  pad_cfg[10]        <= PWDATA[21:16]; //pad_cam_data0
                  pad_cfg[11]        <= PWDATA[29:24]; //pad_cam_data1
                end
                `REG_PADCFG3:
                begin
                  pad_cfg[12]        <= PWDATA[5:0];   //pad_cam_data2
                  pad_cfg[13]        <= PWDATA[13:8];  //pad_cam_data3
                  pad_cfg[14]        <= PWDATA[21:16]; //pad_cam_data4
                  pad_cfg[15]        <= PWDATA[29:24]; //pad_cam_data5
                end
                `REG_PADCFG4:
                begin
                  pad_cfg[16]        <= PWDATA[5:0];   //pad_cam_data6
                  pad_cfg[17]        <= PWDATA[13:8];  //pad_cam_data7
                  pad_cfg[18]        <= PWDATA[21:16]; //pad_cam_hsync
                  pad_cfg[19]        <= PWDATA[29:24]; //pad_cam_vsync
                end
                `REG_PADCFG5:
                begin
                  pad_cfg[20]        <= PWDATA[5:0];   //pad_cam_miso
                  pad_cfg[21]        <= PWDATA[13:8];  //pad_cam_mosi
                  pad_cfg[22]        <= PWDATA[21:16]; //pad_cam_cs
                  pad_cfg[23]        <= PWDATA[29:24]; //pad_cam_sck
                end
                `REG_PADCFG6:
                begin
                  pad_cfg[24]        <= PWDATA[5:0];   //pad_i2c0_sda
                  pad_cfg[25]        <= PWDATA[13:8];  //pad_i2c0_scl
                  pad_cfg[26]        <= PWDATA[21:16]; //pad_i2c1_sda
                  pad_cfg[27]        <= PWDATA[29:24]; //pad_i2c1_scl
                end
                `REG_PADCFG7:
                begin
                  pad_cfg[28]        <= PWDATA[5:0];   //pad_timer0_ch0
                  pad_cfg[29]        <= PWDATA[13:8];  //pad_timer0_ch1
                  pad_cfg[30]        <= PWDATA[21:16]; //pad_timer0_ch2
                  pad_cfg[31]        <= PWDATA[29:24]; //pad_timer0_ch3
                end
                `REG_PADCFG8:
                begin
                  pad_cfg[32]        <= PWDATA[5:0];   //pad_i2s0_sck
                  pad_cfg[33]        <= PWDATA[13:8];  //pad_i2s0_ws
                  pad_cfg[34]        <= PWDATA[21:16]; //pad_i2s0_sdi
                  pad_cfg[35]        <= PWDATA[29:24]; //pad_i2s1_sck
                end
                `REG_PADCFG9:
                begin
                  pad_cfg[36]        <= PWDATA[5:0];   //pad_i2s1_ws
                  pad_cfg[37]        <= PWDATA[13:8];  //pad_i2s1_sdi
                  pad_cfg[38]        <= PWDATA[21:16]; //pad_uart_rx
                  pad_cfg[39]        <= PWDATA[29:24]; //pad_uart_tx
                end
                `REG_PADCFG10:
                begin
                  pad_cfg[40]        <= PWDATA[5:0];   //pad_spim_sdio0
                  pad_cfg[41]        <= PWDATA[13:8];  //pad_spim_sdio1
                  pad_cfg[42]        <= PWDATA[21:16]; //pad_spim_sdio2
                  pad_cfg[43]        <= PWDATA[29:24]; //pad_spim_sdio3
                end
                `REG_PADCFG11:
                begin
                  pad_cfg[44]        <= PWDATA[5:0];   //pad_spim_csn0
                  pad_cfg[45]        <= PWDATA[13:8];  //pad_spim_csn1
                  pad_cfg[46]        <= PWDATA[21:16]; //pad_spim_sck
                  pad_cfg[47]        <= PWDATA[29:24]; //
                end
                `REG_PADCFG12:
                begin
                  pad_cfg[48]        <= PWDATA[5:0];   //
                  pad_cfg[49]        <= PWDATA[13:8];  //
                  pad_cfg[50]        <= PWDATA[21:16]; //
                  pad_cfg[51]        <= PWDATA[29:24]; //
                end
                `REG_PADCFG13:
                begin
                  pad_cfg[52]        <= PWDATA[5:0];   //
                  pad_cfg[53]        <= PWDATA[13:8];  //
                  pad_cfg[54]        <= PWDATA[21:16]; //
                  pad_cfg[55]        <= PWDATA[29:24]; //
                end
                `REG_PADCFG14:
                begin
                  pad_cfg[56]        <= PWDATA[5:0];   //
                  pad_cfg[57]        <= PWDATA[13:8];  //
                  pad_cfg[58]        <= PWDATA[21:16]; //
                  pad_cfg[59]        <= PWDATA[29:24]; //
                end
                `REG_PADCFG15:
                begin
                  pad_cfg[60]        <= PWDATA[5:0];   //
                  pad_cfg[61]        <= PWDATA[13:8];  //
                  pad_cfg[62]        <= PWDATA[21:16]; //
                  pad_cfg[63]        <= PWDATA[29:24]; //
                end
                `REG_JTAGREG:
                begin
                  r_jtag_rego   <= PWDATA[JTAG_REG_SIZE-1:0];
                end
                `REG_CORESTATUS:
                begin
                  r_corestatus  <= PWDATA[31:0];
                end
                `REG_CLUSTER_CTRL:
                begin
                  r_cluster_byp          <= PWDATA[0];
                  r_cluster_pow          <= PWDATA[1];
                  r_cluster_fetch_enable <= PWDATA[2];
                  r_cluster_rstn         <= PWDATA[3];
                end
                `REG_CTRL_PER: begin
`ifdef HYPER_RAM
                    r_sel_hyper_axi <= PWDATA[0];
`endif
                end
                `REG_CLUSTER_IRQ: begin
                    r_cluster_irq <= PWDATA[0];
                end
                `REG_CLUSTER_BOOT_ADDR0:
                    r_cluster_boot[31:0] <= PWDATA;
                `REG_CLUSTER_BOOT_ADDR1:
                    r_cluster_boot[63:32] <= PWDATA;
                default: begin
                `ifndef TARGET_SYNTHESIS
                  `ifdef MSG_VERBOSE
                  $display("[APB SOC CTRL] INVALID WRITE ACCESS to %x at time %t\n",PADDR, $time);
                  `endif
                `endif
                end
          endcase
        end
      end
    end

    // read data
    always_comb
    begin
        PRDATA = '0;
        case (s_apb_addr)
          `REG_PADFUN0:
              for (int i=0;i<16;i++)
              begin
                PRDATA[i*2]   = r_pad_fun0[i];
                PRDATA[i*2+1] = r_pad_fun1[i];
              end
          `REG_PADFUN1:
              for (int i=0;i<16;i++)
              begin
                PRDATA[i*2]   = r_pad_fun0[16+i];
                PRDATA[i*2+1] = r_pad_fun1[16+i];
              end
          `REG_PADFUN2:
              for (int i=0;i<16;i++)
              begin
                PRDATA[i*2]   = r_pad_fun0[32+i];
                PRDATA[i*2+1] = r_pad_fun1[32+i];
              end
          `REG_PADFUN3:
              for (int i=0;i<16;i++)
              begin
                PRDATA[i*2]   = r_pad_fun0[48+i];
                PRDATA[i*2+1] = r_pad_fun1[48+i];
              end
          `REG_PADCFG0:
            PRDATA = {2'b00,pad_cfg[3],2'b00,pad_cfg[2],2'b00,pad_cfg[1],2'b00,pad_cfg[0]};
          `REG_PADCFG1:
            PRDATA = {2'b00,pad_cfg[7],2'b00,pad_cfg[6],2'b00,pad_cfg[5],2'b00,pad_cfg[4]};
          `REG_PADCFG2:
            PRDATA = {2'b00,pad_cfg[11],2'b00,pad_cfg[10],2'b00,pad_cfg[9],2'b00,pad_cfg[8]};
          `REG_PADCFG3:
            PRDATA = {2'b00,pad_cfg[15],2'b00,pad_cfg[14],2'b00,pad_cfg[13],2'b00,pad_cfg[12]};
          `REG_PADCFG4:
            PRDATA = {2'b00,pad_cfg[19],2'b00,pad_cfg[18],2'b00,pad_cfg[17],2'b00,pad_cfg[16]};
          `REG_PADCFG5:
            PRDATA = {2'b00,pad_cfg[23],2'b00,pad_cfg[22],2'b00,pad_cfg[21],2'b00,pad_cfg[20]};
          `REG_PADCFG6:
            PRDATA = {2'b00,pad_cfg[27],2'b00,pad_cfg[26],2'b00,pad_cfg[25],2'b00,pad_cfg[24]};
          `REG_PADCFG7:
            PRDATA = {2'b00,pad_cfg[31],2'b00,pad_cfg[30],2'b00,pad_cfg[29],2'b00,pad_cfg[28]};
          `REG_PADCFG8:
            PRDATA = {2'b00,pad_cfg[35],2'b00,pad_cfg[34],2'b00,pad_cfg[33],2'b00,pad_cfg[32]};
          `REG_PADCFG9:
            PRDATA = {2'b00,pad_cfg[39],2'b00,pad_cfg[38],2'b00,pad_cfg[37],2'b00,pad_cfg[36]};
          `REG_PADCFG10:
            PRDATA = {2'b00,pad_cfg[43],2'b00,pad_cfg[42],2'b00,pad_cfg[41],2'b00,pad_cfg[40]};
          `REG_PADCFG11:
            PRDATA = {2'b00,pad_cfg[47],2'b00,pad_cfg[46],2'b00,pad_cfg[45],2'b00,pad_cfg[44]};
          `REG_PADCFG12:
            PRDATA = {2'b00,pad_cfg[51],2'b00,pad_cfg[50],2'b00,pad_cfg[49],2'b00,pad_cfg[48]};
          `REG_PADCFG13:
            PRDATA = {2'b00,pad_cfg[55],2'b00,pad_cfg[54],2'b00,pad_cfg[53],2'b00,pad_cfg[52]};
          `REG_PADCFG14:
            PRDATA = {2'b00,pad_cfg[59],2'b00,pad_cfg[58],2'b00,pad_cfg[57],2'b00,pad_cfg[56]};
          `REG_PADCFG15:
            PRDATA = {2'b00,pad_cfg[63],2'b00,pad_cfg[62],2'b00,pad_cfg[61],2'b00,pad_cfg[60]};
          `REG_FCBOOT:
            PRDATA = r_bootaddr;
          `REG_INFO:
            PRDATA = {n_cores,n_clusters};
          `REG_CORESTATUS:
            PRDATA = r_corestatus;
          `REG_CS_RO:
            PRDATA = r_corestatus;
          `REG_BOOTSEL:
            PRDATA =  {30'h0, r_bootsel};
          `REG_CLKSEL:
            PRDATA = {31'h0,sel_fll_clk_i};
          `REG_CLUSTER_CTRL:
            PRDATA = {
              29'h0,
              r_cluster_rstn,
              r_cluster_fetch_enable,
              r_cluster_pow,
              r_cluster_byp };
          `REG_JTAGREG:
            PRDATA = {16'h0,r_jtag_regi_sync[0],r_jtag_rego};
          `REG_CTRL_PER:
            PRDATA = {31'b0, r_sel_hyper_axi};
          `REG_CLUSTER_IRQ:
            PRDATA = {31'b0, r_cluster_irq};
          `REG_CLUSTER_BOOT_ADDR0:
            PRDATA = r_cluster_boot[31:0];
          `REG_CLUSTER_BOOT_ADDR1:
            PRDATA = r_cluster_boot[63:32];
          default:
            begin
            PRDATA = 'h0;
            `ifndef TARGET_SYNTHESIS
              `ifdef MSG_VERBOSE
              $display("[APB SOC CTRL] INVALID READ ACCESS to %x at time %t\n",PADDR, $time);
              `endif
            `endif
            end
        endcase
    end

   always_ff @(posedge HCLK, negedge HRESETn)
    begin
      if(~HRESETn) begin
        r_bootsel <= 2'b00;
      end
      else
      begin
        r_bootsel <= {r_bootsel[0],bootsel_i};
      end
    end


   assign n_cores    = NB_CORES;
   assign n_clusters = NB_CLUSTERS;

   assign PREADY     = 1'b1;
   assign PSLVERR    = 1'b0;

endmodule
