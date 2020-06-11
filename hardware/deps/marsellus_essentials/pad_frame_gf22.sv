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

`define DRV_SIG   .NDIN(1'b0), .NDOUT(), .DRV(2'b10), .PWROK(PWROK_S), .IOPWROK(IOPWROK_S), .BIAS(BIAS_S), .RETC(RETC_S)
`define DRV_SIG_I .NDIN(1'b0), .NDOUT(),              .PWROK(PWROK_S), .IOPWROK(IOPWROK_S), .BIAS(BIAS_S), .RETC(RETC_S)


/*
    TODO:

        Check Trigger Schmitt, pull up/down and control and mode signals

        --> Input Only Pad does not have pull up or down
        --> There exists pads with programmable crystal oscillator pads
        (IN22FDX_GPIO18_10M3S30P_POSC_I / IN22FDX_GPIO18_10M3S30P_POSC_O

*/
//`define REDUNDANT_PINS
`define QUENTIN_CHIP

module pad_frame_gf22
    (
    `ifndef REDUNDANT_PINS
        // CONFIGURATION SIGNALS
        `ifndef QUENTIN_CHIP
        input logic [47:0][5:0] cfg_pad_i          ,
        `else
        input logic             pd_hyper_dq0_i     ,
        input logic             pd_hyper_dq1_i     ,
        input logic             pd_hyper_dq2_i     ,
        input logic             pd_hyper_dq3_i     ,
        input logic             pd_hyper_dq4_i     ,
        input logic             pd_hyper_dq5_i     ,
        input logic             pd_hyper_dq6_i     ,
        input logic             pd_hyper_dq7_i     ,
        input logic             pd_hyper_rwds_i    ,
        input logic             pd_hyper_ckn_i     ,
        input logic             pd_hyper_ck_i      ,
        input logic             pd_hyper_csn0_i    ,
        input logic             pd_hyper_csn1_i    ,
        input logic             pd_spim_sck_i      ,
        input logic             pd_spim_sdio0_i    ,
        input logic             pd_spim_sdio1_i    ,
        input logic             pd_spim_sdio2_i    ,
        input logic             pd_spim_sdio3_i    ,
        input logic             pd_spim_csn1_i     ,
        input logic             pd_spim_csn0_i     ,
        input logic             pd_i2s1_sdi_i      ,
        input logic             pd_i2s0_ws_i       ,
        input logic             pd_i2s0_sdi_i      ,
        input logic             pd_i2s0_sck_i      ,
        input logic             pd_cam_pclk_i      ,
        input logic             pd_cam_hsync_i     ,
        input logic             pd_cam_data0_i     ,
        input logic             pd_cam_data1_i     ,
        input logic             pd_cam_data2_i     ,
        input logic             pd_cam_data3_i     ,
        input logic             pd_cam_data4_i     ,
        input logic             pd_cam_data5_i     ,
        input logic             pd_cam_data6_i     ,
        input logic             pd_cam_data7_i     ,
        input logic             pd_cam_vsync_i     ,
        input logic             pd_i2c0_sda_i      ,
        input logic             pd_i2c0_scl_i      ,
        input logic             pu_uart_rx_i       ,
        input logic             pu_uart_tx_i       ,
        `endif

        input logic             oe_spim_sdio0_i    ,
        input logic             oe_spim_sdio1_i    ,
        input logic             oe_spim_sdio2_i    ,
        input logic             oe_spim_sdio3_i    ,
        input logic             oe_spim_csn0_i     ,
        input logic             oe_spim_csn1_i     ,
        input logic             oe_spim_sck_i      ,
        input logic             oe_uart_rx_i       ,
        input logic             oe_uart_tx_i       ,
        input logic             oe_cam_pclk_i      ,
        input logic             oe_cam_hsync_i     ,
        input logic             oe_cam_data0_i     ,
        input logic             oe_cam_data1_i     ,
        input logic             oe_cam_data2_i     ,
        input logic             oe_cam_data3_i     ,
        input logic             oe_cam_data4_i     ,
        input logic             oe_cam_data5_i     ,
        input logic             oe_cam_data6_i     ,
        input logic             oe_cam_data7_i     ,
        input logic             oe_cam_vsync_i     ,
        input logic             oe_hyper_ckn_i     ,
        input logic             oe_hyper_ck_i      ,
        input logic             oe_hyper_dq0_i     ,
        input logic             oe_hyper_dq1_i     ,
        input logic             oe_hyper_dq2_i     ,
        input logic             oe_hyper_dq3_i     ,
        input logic             oe_hyper_dq4_i     ,
        input logic             oe_hyper_dq5_i     ,
        input logic             oe_hyper_dq6_i     ,
        input logic             oe_hyper_dq7_i     ,
        input logic             oe_hyper_csn0_i    ,
        input logic             oe_hyper_csn1_i    ,
        input logic             oe_hyper_rwds_i    ,
        input logic             oe_i2c0_sda_i      ,
        input logic             oe_i2c0_scl_i      ,
        input logic             oe_i2s0_sck_i      ,
        input logic             oe_i2s0_ws_i       ,
        input logic             oe_i2s0_sdi_i      ,
        input logic             oe_i2s1_sdi_i      ,

    `else
        input logic             pd_hyper_dq0_i     ,
        input logic             pd_hyper_dq1_i     ,
        input logic             pd_hyper_dq2_i     ,
        input logic             pd_hyper_dq3_i     ,
        input logic             pd_hyper_dq4_i     ,
        input logic             pd_hyper_dq5_i     ,
        input logic             pd_hyper_dq6_i     ,
        input logic             pd_hyper_dq7_i     ,
        input logic             pd_hyper_rwds_i    ,
        input logic             pd_hyper_ckn_i     ,
        input logic             pd_hyper_ck_i      ,
        input logic             pd_hyper_csn0_i    ,
        input logic             pd_hyper_csn1_i    ,
        input logic             pd_spim_sdio1_i    ,
        input logic             pd_spim_sdio2_i    ,
        input logic             pd_spim_sdio3_i    ,
        input logic             pd_spim_csn1_i     ,
        input logic             pd_spim_csn0_i     ,
        input logic             pd_i2s1_sdi_i      ,
        input logic             pd_i2s0_ws_i       ,
        input logic             pd_i2s0_sdi_i      ,
        input logic             pd_i2s0_sck_i      ,
        input logic             pd_jtag_tck_i      ,
        input logic             pd_jtag_tms_i      ,
        input logic             pd_jtag_tdi_i      ,
        input logic             pd_jtag_trstn_i    ,
        input logic             pd_jtag_tdo_i      ,
        input logic             pd_cam_pclk_i      ,
        input logic             pd_cam_hsync_i     ,
        input logic             pd_cam_data0_i     ,
        input logic             pd_cam_data1_i     ,
        input logic             pd_cam_data2_i     ,
        input logic             pd_cam_data3_i     ,
        input logic             pd_cam_data4_i     ,
        input logic             pd_cam_data5_i     ,
        input logic             pd_cam_data6_i     ,
        input logic             pd_cam_data7_i     ,
        input logic             pd_cam_vsync_i     ,
        input logic             pd_spim_sck_i      ,
        input logic             pd_spim_sdio0_i    ,
        input logic             pd_uart_rx_i       ,
        input logic             pd_uart_tx_i       ,
        input logic             pd_i2c0_sda_i      ,
        input logic             pd_i2c0_scl_i      ,
        input logic             pd_reset_n_i       ,
        input logic             pd_ref_clk_i       ,

        input logic             pu_hyper_dq0_i     ,
        input logic             pu_hyper_dq1_i     ,
        input logic             pu_hyper_dq2_i     ,
        input logic             pu_hyper_dq3_i     ,
        input logic             pu_hyper_dq4_i     ,
        input logic             pu_hyper_dq5_i     ,
        input logic             pu_hyper_dq6_i     ,
        input logic             pu_hyper_dq7_i     ,
        input logic             pu_hyper_rwds_i    ,
        input logic             pu_hyper_ckn_i     ,
        input logic             pu_hyper_ck_i      ,
        input logic             pu_hyper_csn0_i    ,
        input logic             pu_hyper_csn1_i    ,
        input logic             pu_spim_sdio1_i    ,
        input logic             pu_spim_sdio2_i    ,
        input logic             pu_spim_sdio3_i    ,
        input logic             pu_spim_csn1_i     ,
        input logic             pu_spim_csn0_i     ,
        input logic             pu_i2s1_sdi_i      ,
        input logic             pu_i2s0_ws_i       ,
        input logic             pu_i2s0_sdi_i      ,
        input logic             pu_i2s0_sck_i      ,
        input logic             pu_jtag_tck_i      ,
        input logic             pu_jtag_tms_i      ,
        input logic             pu_jtag_tdi_i      ,
        input logic             pu_jtag_trstn_i    ,
        input logic             pu_jtag_tdo_i      ,
        input logic             pu_cam_pclk_i      ,
        input logic             pu_cam_hsync_i     ,
        input logic             pu_cam_data0_i     ,
        input logic             pu_cam_data1_i     ,
        input logic             pu_cam_data2_i     ,
        input logic             pu_cam_data3_i     ,
        input logic             pu_cam_data4_i     ,
        input logic             pu_cam_data5_i     ,
        input logic             pu_cam_data6_i     ,
        input logic             pu_cam_data7_i     ,
        input logic             pu_cam_vsync_i     ,
        input logic             pu_spim_sck_i      ,
        input logic             pu_spim_sdio0_i    ,
        input logic             pu_uart_rx_i       ,
        input logic             pu_uart_tx_i       ,
        input logic             pu_i2c0_sda_i      ,
        input logic             pu_i2c0_scl_i      ,
        input logic             pu_reset_n_i       ,
        input logic             pu_ref_clk_i       ,

        input logic             trien_hyper_dq0_i  ,
        input logic             trien_hyper_dq1_i  ,
        input logic             trien_hyper_dq2_i  ,
        input logic             trien_hyper_dq3_i  ,
        input logic             trien_hyper_dq4_i  ,
        input logic             trien_hyper_dq5_i  ,
        input logic             trien_hyper_dq6_i  ,
        input logic             trien_hyper_dq7_i  ,
        input logic             trien_hyper_rwds_i ,
        input logic             trien_hyper_ckn_i  ,
        input logic             trien_hyper_ck_i   ,
        input logic             trien_hyper_csn0_i ,
        input logic             trien_hyper_csn1_i ,
        input logic             trien_spim_sdio1_i ,
        input logic             trien_spim_sdio2_i ,
        input logic             trien_spim_sdio3_i ,
        input logic             trien_spim_csn1_i  ,
        input logic             trien_spim_csn0_i  ,
        input logic             trien_i2s1_sdi_i   ,
        input logic             trien_i2s0_ws_i    ,
        input logic             trien_i2s0_sdi_i   ,
        input logic             trien_i2s0_sck_i   ,
        input logic             trien_jtag_tck_i   ,
        input logic             trien_jtag_tms_i   ,
        input logic             trien_jtag_tdi_i   ,
        input logic             trien_jtag_trstn_i ,
        input logic             trien_jtag_tdo_i   ,
        input logic             trien_cam_pclk_i   ,
        input logic             trien_cam_hsync_i  ,
        input logic             trien_cam_data0_i  ,
        input logic             trien_cam_data1_i  ,
        input logic             trien_cam_data2_i  ,
        input logic             trien_cam_data3_i  ,
        input logic             trien_cam_data4_i  ,
        input logic             trien_cam_data5_i  ,
        input logic             trien_cam_data6_i  ,
        input logic             trien_cam_data7_i  ,
        input logic             trien_cam_vsync_i  ,
        input logic             trien_spim_sck_i   ,
        input logic             trien_spim_sdio0_i ,
        input logic             trien_uart_rx_i    ,
        input logic             trien_uart_tx_i    ,
        input logic             trien_i2c0_sda_i   ,
        input logic             trien_i2c0_scl_i   ,
        input logic             trien_reset_n_i    ,
        input logic             trien_ref_clk_i    ,

        input logic             rxen_hyper_dq0_i   ,
        input logic             rxen_hyper_dq1_i   ,
        input logic             rxen_hyper_dq2_i   ,
        input logic             rxen_hyper_dq3_i   ,
        input logic             rxen_hyper_dq4_i   ,
        input logic             rxen_hyper_dq5_i   ,
        input logic             rxen_hyper_dq6_i   ,
        input logic             rxen_hyper_dq7_i   ,
        input logic             rxen_hyper_rwds_i  ,
        input logic             rxen_hyper_ckn_i   ,
        input logic             rxen_hyper_ck_i    ,
        input logic             rxen_hyper_csn0_i  ,
        input logic             rxen_hyper_csn1_i  ,
        input logic             rxen_spim_sdio1_i  ,
        input logic             rxen_spim_sdio2_i  ,
        input logic             rxen_spim_sdio3_i  ,
        input logic             rxen_spim_csn1_i   ,
        input logic             rxen_spim_csn0_i   ,
        input logic             rxen_i2s1_sdi_i    ,
        input logic             rxen_i2s0_ws_i     ,
        input logic             rxen_i2s0_sdi_i    ,
        input logic             rxen_i2s0_sck_i    ,
        input logic             rxen_jtag_tck_i    ,
        input logic             rxen_jtag_tms_i    ,
        input logic             rxen_jtag_tdi_i    ,
        input logic             rxen_jtag_trstn_i  ,
        input logic             rxen_jtag_tdo_i    ,
        input logic             rxen_cam_pclk_i    ,
        input logic             rxen_cam_hsync_i   ,
        input logic             rxen_cam_data0_i   ,
        input logic             rxen_cam_data1_i   ,
        input logic             rxen_cam_data2_i   ,
        input logic             rxen_cam_data3_i   ,
        input logic             rxen_cam_data4_i   ,
        input logic             rxen_cam_data5_i   ,
        input logic             rxen_cam_data6_i   ,
        input logic             rxen_cam_data7_i   ,
        input logic             rxen_cam_vsync_i   ,
        input logic             rxen_spim_sck_i    ,
        input logic             rxen_spim_sdio0_i  ,
        input logic             rxen_uart_rx_i     ,
        input logic             rxen_uart_tx_i     ,
        input logic             rxen_i2c0_sda_i    ,
        input logic             rxen_i2c0_scl_i    ,
        input logic             rxen_reset_n_i     ,
        input logic             rxen_ref_clk_i     ,
    `endif

        // REF CLOCK
        output logic            ref_clk_o        ,

        // RESET SIGNALS
        output logic            rstn_o           ,

        // JTAG SIGNALS
        output logic            jtag_tck_o       ,
        output logic            jtag_tdi_o       ,
        input  logic            jtag_tdo_i       ,
        output logic            jtag_tms_o       ,
        output logic            jtag_trst_o      ,

        // INPUTS SIGNALS TO THE PADS
        input logic             out_spim_sdio0_i ,
        input logic             out_spim_sdio1_i ,
        input logic             out_spim_sdio2_i ,
        input logic             out_spim_sdio3_i ,
        input logic             out_spim_csn0_i  ,
        input logic             out_spim_csn1_i  ,
        input logic             out_spim_sck_i   ,
        input logic             out_uart_rx_i    ,
        input logic             out_uart_tx_i    ,
        input logic             out_cam_pclk_i   ,
        input logic             out_cam_hsync_i  ,
        input logic             out_cam_data0_i  ,
        input logic             out_cam_data1_i  ,
        input logic             out_cam_data2_i  ,
        input logic             out_cam_data3_i  ,
        input logic             out_cam_data4_i  ,
        input logic             out_cam_data5_i  ,
        input logic             out_cam_data6_i  ,
        input logic             out_cam_data7_i  ,
        input logic             out_cam_vsync_i  ,
        input logic             out_hyper_ckn_i  ,
        input logic             out_hyper_ck_i   ,
        input logic             out_hyper_dq0_i  ,
        input logic             out_hyper_dq1_i  ,
        input logic             out_hyper_dq2_i  ,
        input logic             out_hyper_dq3_i  ,
        input logic             out_hyper_dq4_i  ,
        input logic             out_hyper_dq5_i  ,
        input logic             out_hyper_dq6_i  ,
        input logic             out_hyper_dq7_i  ,
        input logic             out_hyper_csn0_i ,
        input logic             out_hyper_csn1_i ,
        input logic             out_hyper_rwds_i ,
        input logic             out_i2c0_sda_i   ,
        input logic             out_i2c0_scl_i   ,
        input logic             out_i2s0_sck_i   ,
        input logic             out_i2s0_ws_i    ,
        input logic             out_i2s0_sdi_i   ,
        input logic             out_i2s1_sdi_i   ,

        // OUTPUT SIGNALS FROM THE PADS
        output logic            in_spim_sdio0_o  ,
        output logic            in_spim_sdio1_o  ,
        output logic            in_spim_sdio2_o  ,
        output logic            in_spim_sdio3_o  ,
        output logic            in_spim_csn0_o   ,
        output logic            in_spim_csn1_o   ,
        output logic            in_spim_sck_o    ,
        output logic            in_uart_rx_o     ,
        output logic            in_uart_tx_o     ,
        output logic            in_cam_pclk_o    ,
        output logic            in_cam_hsync_o   ,
        output logic            in_cam_data0_o   ,
        output logic            in_cam_data1_o   ,
        output logic            in_cam_data2_o   ,
        output logic            in_cam_data3_o   ,
        output logic            in_cam_data4_o   ,
        output logic            in_cam_data5_o   ,
        output logic            in_cam_data6_o   ,
        output logic            in_cam_data7_o   ,
        output logic            in_cam_vsync_o   ,
        output logic            in_hyper_ckn_o   ,
        output logic            in_hyper_ck_o    ,
        output logic            in_hyper_dq0_o   ,
        output logic            in_hyper_dq1_o   ,
        output logic            in_hyper_dq2_o   ,
        output logic            in_hyper_dq3_o   ,
        output logic            in_hyper_dq4_o   ,
        output logic            in_hyper_dq5_o   ,
        output logic            in_hyper_dq6_o   ,
        output logic            in_hyper_dq7_o   ,
        output logic            in_hyper_csn0_o  ,
        output logic            in_hyper_csn1_o  ,
        output logic            in_hyper_rwds_o  ,
        output logic            in_i2c0_sda_o    ,
        output logic            in_i2c0_scl_o    ,
        output logic            in_i2s0_sck_o    ,
        output logic            in_i2s0_ws_o     ,
        output logic            in_i2s0_sdi_o    ,
        output logic            in_i2s1_sdi_o    ,

        // EXT CHIP TP PADS
        inout wire              pad_spim_sdio0   ,
        inout wire              pad_spim_sdio1   ,
        inout wire              pad_spim_sdio2   ,
        inout wire              pad_spim_sdio3   ,
        inout wire              pad_spim_csn0    ,
        inout wire              pad_spim_csn1    ,
        inout wire              pad_spim_sck     ,
        inout wire              pad_uart_rx      ,
        inout wire              pad_uart_tx      ,
        inout wire              pad_cam_pclk     ,
        inout wire              pad_cam_hsync    ,
        inout wire              pad_cam_data0    ,
        inout wire              pad_cam_data1    ,
        inout wire              pad_cam_data2    ,
        inout wire              pad_cam_data3    ,
        inout wire              pad_cam_data4    ,
        inout wire              pad_cam_data5    ,
        inout wire              pad_cam_data6    ,
        inout wire              pad_cam_data7    ,
        inout wire              pad_cam_vsync    ,
        inout wire              pad_hyper_ckn    ,
        inout wire              pad_hyper_ck     ,
        inout wire              pad_hyper_dq0    ,
        inout wire              pad_hyper_dq1    ,
        inout wire              pad_hyper_dq2    ,
        inout wire              pad_hyper_dq3    ,
        inout wire              pad_hyper_dq4    ,
        inout wire              pad_hyper_dq5    ,
        inout wire              pad_hyper_dq6    ,
        inout wire              pad_hyper_dq7    ,
        inout wire              pad_hyper_csn0   ,
        inout wire              pad_hyper_csn1   ,
        inout wire              pad_hyper_rwds   ,
        inout wire              pad_i2c0_sda     ,
        inout wire              pad_i2c0_scl     ,
        inout wire              pad_i2s0_sck     ,
        inout wire              pad_i2s0_ws      ,
        inout wire              pad_i2s0_sdi     ,
        inout wire              pad_i2s1_sdi     ,
        //inout wire              pad_por_n        ,
        inout wire              pad_reset_n      ,
        inout wire              pad_bootsel      ,
        inout wire              pad_jtag_tck     ,
        inout wire              pad_jtag_tdi     ,
        inout wire              pad_jtag_tdo     ,
        inout wire              pad_jtag_tms     ,
        inout wire              pad_jtag_trst    ,
        inout wire              pad_xtal_in
    );

    wire PWROK_S, IOPWROK_S, BIAS_S, RETC_S;

    //PDDW12DGZ_G <-> pad_PD_V / H
        //Tri-State Output Pad with Input and Enable Controlled Pull-Down, Fail-Safe

    //PDDW12SDGZ_G <-> IN22FDX_GPIO18_10M3S30P_IO_V / H
        //Tri-State Output Pad with Schmitt Trigger Input and Enable Controlled Pull-Down, Fail-Safe
        /*
    ``````3.2.4 IN22FDX_GPIO18_10M3S30P_IO
        General purpose I/O-pad includes, Schmitt Trigger, programmable driver, pull-up/down resistor as well
        as HBM and CDM ESD protection. P+/Nwell diode placed in between PAD and VDDIO, N+/SX diode
        */

    //PDUW04DGZ_G <-> IN22FDX_GPIO18_10M3S30P_IO_V / H
        //Tri-State Output Pad with Input and Enable Controlled Pull-Up, Fail-Safe

    //PDUW04SDGZ_G <-> IN22FDX_GPIO18_10M3S30P_IO_V / H
        //Tri-State Output Pad with Schmitt Trigger Input and Enable Controlled Pull-Up, Fail-Safe

    //PDUW12DGZ_G <-> IN22FDX_GPIO18_10M3S30P_IO_V / H
        //Tri-State Output Pad with Input and Enable Controlled Pull-Up, Fail-Safe (slower)

//TX Mode
    // RXEN 0 TRIEN 0
//TX RX are Off
    // RXEN 0 TRIEN 1
//Loop Back
    // RXEN 1 TRIEN 0
//RX Mode
    // RXEN 1 TRIEN 1

//oe_* = 0 --> TRIEN = 1, RXEN = 1 --> RX Mode
//oe_* = 1 --> TRIEN = 0, RXEN = 0 --> TX Mode

//Left Pad (Horizontal)

`ifndef REDUNDANT_PINS

    `ifdef QUENTIN_CHIP
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_dq0  (.TRIEN(~oe_hyper_dq0_i ), .DATA(out_hyper_dq0_i ), .RXEN(~oe_hyper_dq0_i ), .Y(in_hyper_dq0_o ), .PAD(pad_hyper_dq0 ), .PDEN(pd_hyper_dq0_i ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_dq1  (.TRIEN(~oe_hyper_dq1_i ), .DATA(out_hyper_dq1_i ), .RXEN(~oe_hyper_dq1_i ), .Y(in_hyper_dq1_o ), .PAD(pad_hyper_dq1 ), .PDEN(pd_hyper_dq1_i ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_dq2  (.TRIEN(~oe_hyper_dq2_i ), .DATA(out_hyper_dq2_i ), .RXEN(~oe_hyper_dq2_i ), .Y(in_hyper_dq2_o ), .PAD(pad_hyper_dq2 ), .PDEN(pd_hyper_dq2_i ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_dq3  (.TRIEN(~oe_hyper_dq3_i ), .DATA(out_hyper_dq3_i ), .RXEN(~oe_hyper_dq3_i ), .Y(in_hyper_dq3_o ), .PAD(pad_hyper_dq3 ), .PDEN(pd_hyper_dq3_i ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_dq4  (.TRIEN(~oe_hyper_dq4_i ), .DATA(out_hyper_dq4_i ), .RXEN(~oe_hyper_dq4_i ), .Y(in_hyper_dq4_o ), .PAD(pad_hyper_dq4 ), .PDEN(pd_hyper_dq4_i ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_dq5  (.TRIEN(~oe_hyper_dq5_i ), .DATA(out_hyper_dq5_i ), .RXEN(~oe_hyper_dq5_i ), .Y(in_hyper_dq5_o ), .PAD(pad_hyper_dq5 ), .PDEN(pd_hyper_dq5_i ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_dq6  (.TRIEN(~oe_hyper_dq6_i ), .DATA(out_hyper_dq6_i ), .RXEN(~oe_hyper_dq6_i ), .Y(in_hyper_dq6_o ), .PAD(pad_hyper_dq6 ), .PDEN(pd_hyper_dq6_i ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_dq7  (.TRIEN(~oe_hyper_dq7_i ), .DATA(out_hyper_dq7_i ), .RXEN(~oe_hyper_dq7_i ), .Y(in_hyper_dq7_o ), .PAD(pad_hyper_dq7 ), .PDEN(pd_hyper_dq7_i ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_rwds (.TRIEN(~oe_hyper_rwds_i), .DATA(out_hyper_rwds_i), .RXEN(~oe_hyper_rwds_i), .Y(in_hyper_rwds_o), .PAD(pad_hyper_rwds), .PDEN(pd_hyper_rwds_i), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_ckn  (.TRIEN(~oe_hyper_ckn_i ), .DATA(out_hyper_ckn_i ), .RXEN(~oe_hyper_ckn_i ), .Y(in_hyper_ckn_o ), .PAD(pad_hyper_ckn ), .PDEN(pd_hyper_ckn_i ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_ck   (.TRIEN(~oe_hyper_ck_i  ), .DATA(out_hyper_ck_i  ), .RXEN(~oe_hyper_ck_i  ), .Y(in_hyper_ck_o  ), .PAD(pad_hyper_ck  ), .PDEN(pd_hyper_ck_i  ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_csn0 (.TRIEN(~oe_hyper_csn0_i), .DATA(out_hyper_csn0_i), .RXEN(~oe_hyper_csn0_i), .Y(in_hyper_csn0_o), .PAD(pad_hyper_csn0), .PDEN(pd_hyper_csn0_i), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_csn1 (.TRIEN(~oe_hyper_csn1_i), .DATA(out_hyper_csn1_i), .RXEN(~oe_hyper_csn1_i), .Y(in_hyper_csn1_o), .PAD(pad_hyper_csn1), .PDEN(pd_hyper_csn1_i), .PUEN(1'b0), `DRV_SIG );

    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_spim_sck   (.TRIEN(~oe_spim_sck_i  ), .DATA(out_spim_sck_i  ), .RXEN(~oe_spim_sck_i  ), .Y(in_spim_sck_o  ), .PAD(pad_spim_sck  ), .PDEN(pd_spim_sck_i  ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_spim_sdio0 (.TRIEN(~oe_spim_sdio0_i), .DATA(out_spim_sdio0_i), .RXEN(~oe_spim_sdio0_i), .Y(in_spim_sdio0_o), .PAD(pad_spim_sdio0), .PDEN(pd_spim_sdio0_i), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_spim_sdio1 (.TRIEN(~oe_spim_sdio1_i), .DATA(out_spim_sdio1_i), .RXEN(~oe_spim_sdio1_i), .Y(in_spim_sdio1_o), .PAD(pad_spim_sdio1), .PDEN(pd_spim_sdio1_i), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_spim_sdio2 (.TRIEN(~oe_spim_sdio2_i), .DATA(out_spim_sdio2_i), .RXEN(~oe_spim_sdio2_i), .Y(in_spim_sdio2_o), .PAD(pad_spim_sdio2), .PDEN(pd_spim_sdio2_i), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_spim_sdio3 (.TRIEN(~oe_spim_sdio3_i), .DATA(out_spim_sdio3_i), .RXEN(~oe_spim_sdio3_i), .Y(in_spim_sdio3_o), .PAD(pad_spim_sdio3), .PDEN(pd_spim_sdio3_i), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_spim_csn1  (.TRIEN(~oe_spim_csn1_i ), .DATA(out_spim_csn1_i ), .RXEN(~oe_spim_csn1_i ), .Y(in_spim_csn1_o ), .PAD(pad_spim_csn1 ), .PDEN(pd_spim_csn1_i ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_spim_csn0  (.TRIEN(~oe_spim_csn0_i ), .DATA(out_spim_csn0_i ), .RXEN(~oe_spim_csn0_i ), .Y(in_spim_csn0_o ), .PAD(pad_spim_csn0 ), .PDEN(pd_spim_csn0_i ), .PUEN(1'b0), `DRV_SIG );

    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_i2s1_sdi   (.TRIEN(~oe_i2s1_sdi_i  ), .DATA(out_i2s1_sdi_i  ), .RXEN(~oe_i2s1_sdi_i  ), .Y(in_i2s1_sdi_o  ), .PAD(pad_i2s1_sdi  ), .PDEN(pd_i2s1_sdi_i  ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_i2s0_ws    (.TRIEN(~oe_i2s0_ws_i   ), .DATA(out_i2s0_ws_i   ), .RXEN(~oe_i2s0_ws_i   ), .Y(in_i2s0_ws_o   ), .PAD(pad_i2s0_ws   ), .PDEN(pd_i2s0_ws_i   ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_i2s0_sdi   (.TRIEN(~oe_i2s0_sdi_i  ), .DATA(out_i2s0_sdi_i  ), .RXEN(~oe_i2s0_sdi_i  ), .Y(in_i2s0_sdi_o  ), .PAD(pad_i2s0_sdi  ), .PDEN(pd_i2s0_sdi_i  ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_i2s0_sck   (.TRIEN(~oe_i2s0_sck_i  ), .DATA(out_i2s0_sck_i  ), .RXEN(~oe_i2s0_sck_i  ), .Y(in_i2s0_sck_o  ), .PAD(pad_i2s0_sck  ), .PDEN(pd_i2s0_sck_i  ), .PUEN(1'b0), `DRV_SIG );

    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_jtag_tck   (.TRIEN(1'b1            ), .DATA(                ), .RXEN(1'b1            ), .Y(jtag_tck_o     ), .PAD(pad_jtag_tck  ), .PDEN(1'b0           ), .PUEN(1'b1), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_jtag_tms   (.TRIEN(1'b1            ), .DATA(                ), .RXEN(1'b1            ), .Y(jtag_tms_o     ), .PAD(pad_jtag_tms  ), .PDEN(1'b0           ), .PUEN(1'b1), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_jtag_tdi   (.TRIEN(1'b1            ), .DATA(                ), .RXEN(1'b1            ), .Y(jtag_tdi_o     ), .PAD(pad_jtag_tdi  ), .PDEN(1'b0           ), .PUEN(1'b1), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_jtag_trstn (.TRIEN(1'b1            ), .DATA(                ), .RXEN(1'b1            ), .Y(jtag_trst_o    ), .PAD(pad_jtag_trst ), .PDEN(1'b0           ), .PUEN(1'b1), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_jtag_tdo   (.TRIEN(1'b0            ), .DATA(jtag_tdo_i      ), .RXEN(1'b0            ), .Y(               ), .PAD(pad_jtag_tdo  ), .PDEN(1'b1           ), .PUEN(1'b0), `DRV_SIG );

    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_pclk   (.TRIEN(~oe_cam_pclk_i  ), .DATA(out_cam_pclk_i  ), .RXEN(~oe_cam_pclk_i  ), .Y(in_cam_pclk_o  ), .PAD(pad_cam_pclk  ), .PDEN(pd_cam_pclk_i  ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_hsync  (.TRIEN(~oe_cam_hsync_i ), .DATA(out_cam_hsync_i ), .RXEN(~oe_cam_hsync_i ), .Y(in_cam_hsync_o ), .PAD(pad_cam_hsync ), .PDEN(pd_cam_hsync_i ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_data0  (.TRIEN(~oe_cam_data0_i ), .DATA(out_cam_data0_i ), .RXEN(~oe_cam_data0_i ), .Y(in_cam_data0_o ), .PAD(pad_cam_data0 ), .PDEN(pd_cam_data0_i ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_data1  (.TRIEN(~oe_cam_data1_i ), .DATA(out_cam_data1_i ), .RXEN(~oe_cam_data1_i ), .Y(in_cam_data1_o ), .PAD(pad_cam_data1 ), .PDEN(pd_cam_data1_i ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_data2  (.TRIEN(~oe_cam_data2_i ), .DATA(out_cam_data2_i ), .RXEN(~oe_cam_data2_i ), .Y(in_cam_data2_o ), .PAD(pad_cam_data2 ), .PDEN(pd_cam_data2_i ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_data3  (.TRIEN(~oe_cam_data3_i ), .DATA(out_cam_data3_i ), .RXEN(~oe_cam_data3_i ), .Y(in_cam_data3_o ), .PAD(pad_cam_data3 ), .PDEN(pd_cam_data3_i ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_data4  (.TRIEN(~oe_cam_data4_i ), .DATA(out_cam_data4_i ), .RXEN(~oe_cam_data4_i ), .Y(in_cam_data4_o ), .PAD(pad_cam_data4 ), .PDEN(pd_cam_data4_i ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_data5  (.TRIEN(~oe_cam_data5_i ), .DATA(out_cam_data5_i ), .RXEN(~oe_cam_data5_i ), .Y(in_cam_data5_o ), .PAD(pad_cam_data5 ), .PDEN(pd_cam_data5_i ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_data6  (.TRIEN(~oe_cam_data6_i ), .DATA(out_cam_data6_i ), .RXEN(~oe_cam_data6_i ), .Y(in_cam_data6_o ), .PAD(pad_cam_data6 ), .PDEN(pd_cam_data6_i ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_data7  (.TRIEN(~oe_cam_data7_i ), .DATA(out_cam_data7_i ), .RXEN(~oe_cam_data7_i ), .Y(in_cam_data7_o ), .PAD(pad_cam_data7 ), .PDEN(pd_cam_data7_i ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_vsync  (.TRIEN(~oe_cam_vsync_i ), .DATA(out_cam_vsync_i ), .RXEN(~oe_cam_vsync_i ), .Y(in_cam_vsync_o ), .PAD(pad_cam_vsync ), .PDEN(pd_cam_vsync_i ), .PUEN(1'b0), `DRV_SIG );

    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_uart_rx    (.TRIEN(~oe_uart_rx_i   ), .DATA(out_uart_rx_i   ), .RXEN(~oe_uart_rx_i   ), .Y(in_uart_rx_o   ), .PAD(pad_uart_rx   ), .PUEN(pu_uart_rx_i   ), .PDEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_uart_tx    (.TRIEN(~oe_uart_tx_i   ), .DATA(out_uart_tx_i   ), .RXEN(~oe_uart_tx_i   ), .Y(in_uart_tx_o   ), .PAD(pad_uart_tx   ), .PUEN(pu_uart_tx_i   ), .PDEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_i2c0_sda   (.TRIEN(~oe_i2c0_sda_i  ), .DATA(out_i2c0_sda_i  ), .RXEN(~oe_i2c0_sda_i  ), .Y(in_i2c0_sda_o  ), .PAD(pad_i2c0_sda  ), .PDEN(pd_i2c0_sda_i  ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_i2c0_scl   (.TRIEN(~oe_i2c0_scl_i  ), .DATA(out_i2c0_scl_i  ), .RXEN(~oe_i2c0_scl_i  ), .Y(in_i2c0_scl_o  ), .PAD(pad_i2c0_scl  ), .PDEN(pd_i2c0_scl_i  ), .PUEN(1'b0), `DRV_SIG );

    IN22FDX_GPIO18_10M3S30P_IO_V   padinst_reset_n   (.TRIEN(1'b1            ), .DATA(                ), .RXEN(1'b1            ), .Y(rstn_o         ), .PAD(pad_reset_n   ), .PDEN(1'b0           ), .PUEN(1'b1), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V   padinst_ref_clk   (.TRIEN(1'b1            ), .DATA(                ), .RXEN(1'b1            ), .Y(ref_clk_o      ), .PAD(pad_xtal_in   ), .PDEN(1'b0           ), .PUEN(1'b1), `DRV_SIG );

    `else

    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_dq0  (.TRIEN(~oe_hyper_dq0_i ), .DATA(out_hyper_dq0_i ), .RXEN(~oe_hyper_dq0_i ), .Y(in_hyper_dq0_o ), .PAD(pad_hyper_dq0 ), .PDEN(~cfg_pad_i[22][0]), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_dq1  (.TRIEN(~oe_hyper_dq1_i ), .DATA(out_hyper_dq1_i ), .RXEN(~oe_hyper_dq1_i ), .Y(in_hyper_dq1_o ), .PAD(pad_hyper_dq1 ), .PDEN(~cfg_pad_i[23][0]), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_dq2  (.TRIEN(~oe_hyper_dq2_i ), .DATA(out_hyper_dq2_i ), .RXEN(~oe_hyper_dq2_i ), .Y(in_hyper_dq2_o ), .PAD(pad_hyper_dq2 ), .PDEN(~cfg_pad_i[24][0]), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_dq3  (.TRIEN(~oe_hyper_dq3_i ), .DATA(out_hyper_dq3_i ), .RXEN(~oe_hyper_dq3_i ), .Y(in_hyper_dq3_o ), .PAD(pad_hyper_dq3 ), .PDEN(~cfg_pad_i[25][0]), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_dq4  (.TRIEN(~oe_hyper_dq4_i ), .DATA(out_hyper_dq4_i ), .RXEN(~oe_hyper_dq4_i ), .Y(in_hyper_dq4_o ), .PAD(pad_hyper_dq4 ), .PDEN(~cfg_pad_i[26][0]), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_dq5  (.TRIEN(~oe_hyper_dq5_i ), .DATA(out_hyper_dq5_i ), .RXEN(~oe_hyper_dq5_i ), .Y(in_hyper_dq5_o ), .PAD(pad_hyper_dq5 ), .PDEN(~cfg_pad_i[27][0]), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_dq6  (.TRIEN(~oe_hyper_dq6_i ), .DATA(out_hyper_dq6_i ), .RXEN(~oe_hyper_dq6_i ), .Y(in_hyper_dq6_o ), .PAD(pad_hyper_dq6 ), .PDEN(~cfg_pad_i[28][0]), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_dq7  (.TRIEN(~oe_hyper_dq7_i ), .DATA(out_hyper_dq7_i ), .RXEN(~oe_hyper_dq7_i ), .Y(in_hyper_dq7_o ), .PAD(pad_hyper_dq7 ), .PDEN(~cfg_pad_i[29][0]), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_rwds (.TRIEN(~oe_hyper_rwds_i), .DATA(out_hyper_rwds_i), .RXEN(~oe_hyper_rwds_i), .Y(in_hyper_rwds_o), .PAD(pad_hyper_rwds), .PDEN(~cfg_pad_i[32][0]), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_ckn  (.TRIEN(~oe_hyper_ckn_i ), .DATA(out_hyper_ckn_i ), .RXEN(~oe_hyper_ckn_i ), .Y(in_hyper_ckn_o ), .PAD(pad_hyper_ckn ), .PDEN(~cfg_pad_i[20][0]), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_ck   (.TRIEN(~oe_hyper_ck_i  ), .DATA(out_hyper_ck_i  ), .RXEN(~oe_hyper_ck_i  ), .Y(in_hyper_ck_o  ), .PAD(pad_hyper_ck  ), .PDEN(~cfg_pad_i[21][0]), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_csn0 (.TRIEN(~oe_hyper_csn0_i), .DATA(out_hyper_csn0_i), .RXEN(~oe_hyper_csn0_i), .Y(in_hyper_csn0_o), .PAD(pad_hyper_csn0), .PDEN(~cfg_pad_i[30][0]), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_csn1 (.TRIEN(~oe_hyper_csn1_i), .DATA(out_hyper_csn1_i), .RXEN(~oe_hyper_csn1_i), .Y(in_hyper_csn1_o), .PAD(pad_hyper_csn1), .PDEN(~cfg_pad_i[31][0]), .PUEN(1'b0), `DRV_SIG );

    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_spim_sdio1 (.TRIEN(~oe_spim_sdio1_i), .DATA(out_spim_sdio1_i), .RXEN(~oe_spim_sdio1_i), .Y(in_spim_sdio1_o), .PAD(pad_spim_sdio1), .PDEN(~cfg_pad_i[1][0] ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_spim_sdio2 (.TRIEN(~oe_spim_sdio2_i), .DATA(out_spim_sdio2_i), .RXEN(~oe_spim_sdio2_i), .Y(in_spim_sdio2_o), .PAD(pad_spim_sdio2), .PDEN(~cfg_pad_i[2][0] ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_spim_sdio3 (.TRIEN(~oe_spim_sdio3_i), .DATA(out_spim_sdio3_i), .RXEN(~oe_spim_sdio3_i), .Y(in_spim_sdio3_o), .PAD(pad_spim_sdio3), .PDEN(~cfg_pad_i[3][0] ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_spim_csn1  (.TRIEN(~oe_spim_csn1_i ), .DATA(out_spim_csn1_i ), .RXEN(~oe_spim_csn0_i ), .Y(in_spim_csn1_o ), .PAD(pad_spim_csn1 ), .PDEN(~cfg_pad_i[5][0] ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_spim_csn0  (.TRIEN(~oe_spim_csn0_i ), .DATA(out_spim_csn0_i ), .RXEN(~oe_spim_csn0_i ), .Y(in_spim_csn0_o ), .PAD(pad_spim_csn0 ), .PDEN(~cfg_pad_i[4][0] ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_i2s1_sdi   (.TRIEN(~oe_i2s1_sdi_i  ), .DATA(out_i2s1_sdi_i  ), .RXEN(~oe_i2s1_sdi_i  ), .Y(in_i2s1_sdi_o  ), .PAD(pad_i2s1_sdi  ), .PDEN(~cfg_pad_i[38][0]), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_i2s0_ws    (.TRIEN(~oe_i2s0_ws_i   ), .DATA(out_i2s0_ws_i   ), .RXEN(~oe_i2s0_ws_i   ), .Y(in_i2s0_ws_o   ), .PAD(pad_i2s0_ws   ), .PDEN(~cfg_pad_i[36][0]), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_i2s0_sdi   (.TRIEN(~oe_i2s0_sdi_i  ), .DATA(out_i2s0_sdi_i  ), .RXEN(~oe_i2s0_sdi_i  ), .Y(in_i2s0_sdi_o  ), .PAD(pad_i2s0_sdi  ), .PDEN(~cfg_pad_i[37][0]), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_i2s0_sck   (.TRIEN(~oe_i2s0_sck_i  ), .DATA(out_i2s0_sck_i  ), .RXEN(~oe_i2s0_sck_i  ), .Y(in_i2s0_sck_o  ), .PAD(pad_i2s0_sck  ), .PDEN(~cfg_pad_i[35][0]), .PUEN(1'b0), `DRV_SIG );

    IN22FDX_GPIO18_10M3S30P_I_V   padinst_jtag_tck   (                                                   .RXEN(1'b1             ), .Y(jtag_tck_o     ), .PAD(pad_jtag_tck  ),                                      `DRV_SIG_I);
    IN22FDX_GPIO18_10M3S30P_I_V   padinst_jtag_tms   (                                                   .RXEN(1'b1             ), .Y(jtag_tms_o     ), .PAD(pad_jtag_tms  ),                                      `DRV_SIG_I);
    IN22FDX_GPIO18_10M3S30P_I_V   padinst_jtag_tdi   (                                                   .RXEN(1'b1             ), .Y(jtag_tdi_o     ), .PAD(pad_jtag_tdi  ),                                      `DRV_SIG_I);
    IN22FDX_GPIO18_10M3S30P_I_V   padinst_jtag_trstn (                                                   .RXEN(1'b1             ), .Y(jtag_trst_o    ), .PAD(pad_jtag_trst ),                                      `DRV_SIG_I);
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_jtag_tdo   (.TRIEN(1'b0),             .DATA(jtag_tdo_i     ),  .RXEN(1'b0             ), .Y(               ), .PAD(pad_jtag_tdo  ), .PDEN(1'b1            ), .PUEN(1'b0), `DRV_SIG );

    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_pclk   (.TRIEN(~oe_cam_pclk_i  ), .DATA(out_cam_pclk_i  ), .RXEN(~oe_cam_pclk_i  ), .Y(in_cam_pclk_o  ), .PAD(pad_cam_pclk  ), .PDEN(~cfg_pad_i[9][0] ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_hsync  (.TRIEN(~oe_cam_hsync_i ), .DATA(out_cam_hsync_i ), .RXEN(~oe_cam_hsync_i ), .Y(in_cam_hsync_o ), .PAD(pad_cam_hsync ), .PDEN(~cfg_pad_i[10][0]), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_data0  (.TRIEN(~oe_cam_data0_i ), .DATA(out_cam_data0_i ), .RXEN(~oe_cam_data0_i ), .Y(in_cam_data0_o ), .PAD(pad_cam_data0 ), .PDEN(~cfg_pad_i[11][0]), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_data1  (.TRIEN(~oe_cam_data1_i ), .DATA(out_cam_data1_i ), .RXEN(~oe_cam_data1_i ), .Y(in_cam_data1_o ), .PAD(pad_cam_data1 ), .PDEN(~cfg_pad_i[12][0]), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_data2  (.TRIEN(~oe_cam_data2_i ), .DATA(out_cam_data2_i ), .RXEN(~oe_cam_data2_i ), .Y(in_cam_data2_o ), .PAD(pad_cam_data2 ), .PDEN(~cfg_pad_i[13][0]), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_data3  (.TRIEN(~oe_cam_data3_i ), .DATA(out_cam_data3_i ), .RXEN(~oe_cam_data3_i ), .Y(in_cam_data3_o ), .PAD(pad_cam_data3 ), .PDEN(~cfg_pad_i[14][0]), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_data4  (.TRIEN(~oe_cam_data4_i ), .DATA(out_cam_data4_i ), .RXEN(~oe_cam_data4_i ), .Y(in_cam_data4_o ), .PAD(pad_cam_data4 ), .PDEN(~cfg_pad_i[15][0]), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_data5  (.TRIEN(~oe_cam_data5_i ), .DATA(out_cam_data5_i ), .RXEN(~oe_cam_data5_i ), .Y(in_cam_data5_o ), .PAD(pad_cam_data5 ), .PDEN(~cfg_pad_i[16][0]), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_data6  (.TRIEN(~oe_cam_data6_i ), .DATA(out_cam_data6_i ), .RXEN(~oe_cam_data6_i ), .Y(in_cam_data6_o ), .PAD(pad_cam_data6 ), .PDEN(~cfg_pad_i[17][0]), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_data7  (.TRIEN(~oe_cam_data7_i ), .DATA(out_cam_data7_i ), .RXEN(~oe_cam_data7_i ), .Y(in_cam_data7_o ), .PAD(pad_cam_data7 ), .PDEN(~cfg_pad_i[18][0]), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_vsync  (.TRIEN(~oe_cam_vsync_i ), .DATA(out_cam_vsync_i ), .RXEN(~oe_cam_vsync_i ), .Y(in_cam_vsync_o ), .PAD(pad_cam_vsync ), .PDEN(~cfg_pad_i[19][0]), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_spim_sck   (.TRIEN(~oe_spim_sck_i  ), .DATA(out_spim_sck_i  ), .RXEN(~oe_spim_sck_i  ), .Y(in_spim_sck_o  ), .PAD(pad_spim_sck  ), .PDEN(~cfg_pad_i[6][0] ), .PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_spim_sdio0 (.TRIEN(~oe_spim_sdio0_i), .DATA(out_spim_sdio0_i), .RXEN(~oe_spim_sdio0_i), .Y(in_spim_sdio0_o), .PAD(pad_spim_sdio0), .PDEN(~cfg_pad_i[0][0] ), .PUEN(1'b0), `DRV_SIG );

    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_uart_rx    (.TRIEN(~oe_uart_rx_i   ), .DATA(out_uart_rx_i   ), .RXEN(~oe_uart_rx_i    ), .Y(in_uart_rx_o   ), .PAD(pad_uart_rx   ), .PUEN(~cfg_pad_i[7][0]), .PDEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_uart_tx    (.TRIEN(~oe_uart_tx_i   ), .DATA(out_uart_tx_i   ), .RXEN(~oe_uart_tx_i    ), .Y(in_uart_tx_o   ), .PAD(pad_uart_tx   ), .PUEN(~cfg_pad_i[8][0]), .PDEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_i2c0_sda   (.TRIEN(~oe_i2c0_sda_i  ), .DATA(out_i2c0_sda_i  ), .RXEN(~oe_i2c0_sda_i   ), .Y(in_i2c0_sda_o  ), .PAD(pad_i2c0_sda  ), .PDEN(~cfg_pad_i[33][0]),.PUEN(1'b0), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_i2c0_scl   (.TRIEN(~oe_i2c0_scl_i  ), .DATA(out_i2c0_scl_i  ), .RXEN(~oe_i2c0_scl_i   ), .Y(in_i2c0_scl_o  ), .PAD(pad_i2c0_scl  ), .PDEN(~cfg_pad_i[34][0]),.PUEN(1'b0), `DRV_SIG );

    IN22FDX_GPIO18_10M3S30P_I_V   padinst_reset_n    (                                                   .RXEN(1'b1             ), .Y(rstn_o         ), .PAD(pad_reset_n   ),                                      `DRV_SIG_I);
    IN22FDX_GPIO18_10M3S30P_I_V   padinst_ref_clk    (                                                   .RXEN(1'b1             ), .Y(ref_clk_o      ), .PAD(pad_xtal_in   ),                                      `DRV_SIG_I);
    `endif

`else

    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_dq0  (.TRIEN(trien_hyper_dq0_i ), .DATA(out_hyper_dq0_i ), .RXEN(rxen_hyper_dq0_i ), .Y(in_hyper_dq0_o ), .PAD(pad_hyper_dq0 ), .PDEN(pd_hyper_dq0_i ), .PUEN(pu_hyper_dq0_i ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_dq1  (.TRIEN(trien_hyper_dq1_i ), .DATA(out_hyper_dq1_i ), .RXEN(rxen_hyper_dq1_i ), .Y(in_hyper_dq1_o ), .PAD(pad_hyper_dq1 ), .PDEN(pd_hyper_dq1_i ), .PUEN(pu_hyper_dq1_i ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_dq2  (.TRIEN(trien_hyper_dq2_i ), .DATA(out_hyper_dq2_i ), .RXEN(rxen_hyper_dq2_i ), .Y(in_hyper_dq2_o ), .PAD(pad_hyper_dq2 ), .PDEN(pd_hyper_dq2_i ), .PUEN(pu_hyper_dq2_i ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_dq3  (.TRIEN(trien_hyper_dq3_i ), .DATA(out_hyper_dq3_i ), .RXEN(rxen_hyper_dq3_i ), .Y(in_hyper_dq3_o ), .PAD(pad_hyper_dq3 ), .PDEN(pd_hyper_dq3_i ), .PUEN(pu_hyper_dq3_i ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_dq4  (.TRIEN(trien_hyper_dq4_i ), .DATA(out_hyper_dq4_i ), .RXEN(rxen_hyper_dq4_i ), .Y(in_hyper_dq4_o ), .PAD(pad_hyper_dq4 ), .PDEN(pd_hyper_dq4_i ), .PUEN(pu_hyper_dq4_i ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_dq5  (.TRIEN(trien_hyper_dq5_i ), .DATA(out_hyper_dq5_i ), .RXEN(rxen_hyper_dq5_i ), .Y(in_hyper_dq5_o ), .PAD(pad_hyper_dq5 ), .PDEN(pd_hyper_dq5_i ), .PUEN(pu_hyper_dq5_i ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_dq6  (.TRIEN(trien_hyper_dq6_i ), .DATA(out_hyper_dq6_i ), .RXEN(rxen_hyper_dq6_i ), .Y(in_hyper_dq6_o ), .PAD(pad_hyper_dq6 ), .PDEN(pd_hyper_dq6_i ), .PUEN(pu_hyper_dq6_i ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_dq7  (.TRIEN(trien_hyper_dq7_i ), .DATA(out_hyper_dq7_i ), .RXEN(rxen_hyper_dq7_i ), .Y(in_hyper_dq7_o ), .PAD(pad_hyper_dq7 ), .PDEN(pd_hyper_dq7_i ), .PUEN(pu_hyper_dq7_i ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_rwds (.TRIEN(trien_hyper_rwds_i), .DATA(out_hyper_rwds_i), .RXEN(rxen_hyper_rwds_i), .Y(in_hyper_rwds_o), .PAD(pad_hyper_rwds), .PDEN(pd_hyper_rwds_i), .PUEN(pu_hyper_rwds_i), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_ckn  (.TRIEN(trien_hyper_ckn_i ), .DATA(out_hyper_ckn_i ), .RXEN(rxen_hyper_ckn_i ), .Y(in_hyper_ckn_o ), .PAD(pad_hyper_ckn ), .PDEN(pd_hyper_ckn_i ), .PUEN(pu_hyper_ckn_i ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_ck   (.TRIEN(trien_hyper_ck_i  ), .DATA(out_hyper_ck_i  ), .RXEN(rxen_hyper_ck_i  ), .Y(in_hyper_ck_o  ), .PAD(pad_hyper_ck  ), .PDEN(pd_hyper_ck_i  ), .PUEN(pu_hyper_ck_i  ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_csn0 (.TRIEN(trien_hyper_csn0_i), .DATA(out_hyper_csn0_i), .RXEN(rxen_hyper_csn0_i), .Y(in_hyper_csn0_o), .PAD(pad_hyper_csn0), .PDEN(pd_hyper_csn0_i), .PUEN(pu_hyper_csn0_i), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_hyper_csn1 (.TRIEN(trien_hyper_csn1_i), .DATA(out_hyper_csn1_i), .RXEN(rxen_hyper_csn1_i), .Y(in_hyper_csn1_o), .PAD(pad_hyper_csn1), .PDEN(pd_hyper_csn1_i), .PUEN(pu_hyper_csn1_i), `DRV_SIG );

    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_spim_sdio1 (.TRIEN(trien_spim_sdio1_i), .DATA(out_spim_sdio1_i), .RXEN(rxen_spim_sdio1_i), .Y(in_spim_sdio1_o), .PAD(pad_spim_sdio1), .PDEN(pd_spim_sdio1_i), .PUEN(pu_spim_sdio1_i), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_spim_sdio2 (.TRIEN(trien_spim_sdio2_i), .DATA(out_spim_sdio2_i), .RXEN(rxen_spim_sdio2_i), .Y(in_spim_sdio2_o), .PAD(pad_spim_sdio2), .PDEN(pd_spim_sdio2_i), .PUEN(pu_spim_sdio2_i), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_spim_sdio3 (.TRIEN(trien_spim_sdio3_i), .DATA(out_spim_sdio3_i), .RXEN(rxen_spim_sdio3_i), .Y(in_spim_sdio3_o), .PAD(pad_spim_sdio3), .PDEN(pd_spim_sdio3_i), .PUEN(pu_spim_sdio3_i), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_spim_csn1  (.TRIEN(trien_spim_csn1_i ), .DATA(out_spim_csn1_i ), .RXEN(rxen_spim_csn0_i ), .Y(in_spim_csn1_o ), .PAD(pad_spim_csn1 ), .PDEN(pd_spim_csn0_i ), .PUEN(pu_spim_csn0_i ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_spim_csn0  (.TRIEN(trien_spim_csn0_i ), .DATA(out_spim_csn0_i ), .RXEN(rxen_spim_csn0_i ), .Y(in_spim_csn0_o ), .PAD(pad_spim_csn0 ), .PDEN(pd_spim_csn0_i ), .PUEN(pu_spim_csn0_i ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_i2s1_sdi   (.TRIEN(trien_i2s1_sdi_i  ), .DATA(out_i2s1_sdi_i  ), .RXEN(rxen_i2s1_sdi_i  ), .Y(in_i2s1_sdi_o  ), .PAD(pad_i2s1_sdi  ), .PDEN(pd_i2s1_sdi_i  ), .PUEN(pu_i2s1_sdi_i  ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_i2s0_ws    (.TRIEN(trien_i2s0_ws_i   ), .DATA(out_i2s0_ws_i   ), .RXEN(rxen_i2s0_ws_i   ), .Y(in_i2s0_ws_o   ), .PAD(pad_i2s0_ws   ), .PDEN(pd_i2s0_ws_i   ), .PUEN(pu_i2s0_ws_i   ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_i2s0_sdi   (.TRIEN(trien_i2s0_sdi_i  ), .DATA(out_i2s0_sdi_i  ), .RXEN(rxen_i2s0_sdi_i  ), .Y(in_i2s0_sdi_o  ), .PAD(pad_i2s0_sdi  ), .PDEN(pd_i2s0_sdi_i  ), .PUEN(pu_i2s0_sdi_i  ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_i2s0_sck   (.TRIEN(trien_i2s0_sck_i  ), .DATA(out_i2s0_sck_i  ), .RXEN(rxen_i2s0_sck_i  ), .Y(in_i2s0_sck_o  ), .PAD(pad_i2s0_sck  ), .PDEN(pd_i2s0_sck_i  ), .PUEN(pu_i2s0_sck_i  ), `DRV_SIG );

    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_jtag_tck   (.TRIEN(trien_jtag_tck_i  ), .DATA(                ), .RXEN(rxen_jtag_tck_i  ), .Y(jtag_tck_o     ), .PAD(pad_jtag_tck  ), .PDEN(pd_jtag_tck_i  ), .PUEN(pu_jtag_tck_i  ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_jtag_tms   (.TRIEN(trien_jtag_tms_i  ), .DATA(                ), .RXEN(rxen_jtag_tms_i  ), .Y(jtag_tms_o     ), .PAD(pad_jtag_tms  ), .PDEN(pd_jtag_tms_i  ), .PUEN(pu_jtag_tms_i  ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_jtag_tdi   (.TRIEN(trien_jtag_tdi_i  ), .DATA(                ), .RXEN(rxen_jtag_tdi_i  ), .Y(jtag_tdi_o     ), .PAD(pad_jtag_tdi  ), .PDEN(pd_jtag_tdi_i  ), .PUEN(pu_jtag_tdi_i  ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_jtag_trstn (.TRIEN(trien_jtag_trstn_i), .DATA(                ), .RXEN(rxen_jtag_trstn_i), .Y(jtag_trst_o    ), .PAD(pad_jtag_trst ), .PDEN(pd_jtag_trstn_i), .PUEN(pu_jtag_trstn_i), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_jtag_tdo   (.TRIEN(trien_jtag_tdo_i  ), .DATA(jtag_tdo_i      ), .RXEN(rxen_jtag_tdo_i  ), .Y(               ), .PAD(pad_jtag_tdo  ), .PDEN(pd_jtag_tdo_i  ), .PUEN(pu_jtag_tdo_i  ), `DRV_SIG );

    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_pclk   (.TRIEN(trien_cam_pclk_i  ), .DATA(out_cam_pclk_i  ), .RXEN(rxen_cam_pclk_i  ), .Y(in_cam_pclk_o  ), .PAD(pad_cam_pclk  ), .PDEN(pd_cam_pclk_i  ), .PUEN(pu_cam_pclk_i  ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_hsync  (.TRIEN(trien_cam_hsync_i ), .DATA(out_cam_hsync_i ), .RXEN(rxen_cam_hsync_i ), .Y(in_cam_hsync_o ), .PAD(pad_cam_hsync ), .PDEN(pd_cam_hsync_i ), .PUEN(pu_cam_hsync_i ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_data0  (.TRIEN(trien_cam_data0_i ), .DATA(out_cam_data0_i ), .RXEN(rxen_cam_data0_i ), .Y(in_cam_data0_o ), .PAD(pad_cam_data0 ), .PDEN(pd_cam_data0_i ), .PUEN(pu_cam_data0_i ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_data1  (.TRIEN(trien_cam_data1_i ), .DATA(out_cam_data1_i ), .RXEN(rxen_cam_data1_i ), .Y(in_cam_data1_o ), .PAD(pad_cam_data1 ), .PDEN(pd_cam_data1_i ), .PUEN(pu_cam_data1_i ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_data2  (.TRIEN(trien_cam_data2_i ), .DATA(out_cam_data2_i ), .RXEN(rxen_cam_data2_i ), .Y(in_cam_data2_o ), .PAD(pad_cam_data2 ), .PDEN(pd_cam_data2_i ), .PUEN(pu_cam_data2_i ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_data3  (.TRIEN(trien_cam_data3_i ), .DATA(out_cam_data3_i ), .RXEN(rxen_cam_data3_i ), .Y(in_cam_data3_o ), .PAD(pad_cam_data3 ), .PDEN(pd_cam_data3_i ), .PUEN(pu_cam_data3_i ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_data4  (.TRIEN(trien_cam_data4_i ), .DATA(out_cam_data4_i ), .RXEN(rxen_cam_data4_i ), .Y(in_cam_data4_o ), .PAD(pad_cam_data4 ), .PDEN(pd_cam_data4_i ), .PUEN(pu_cam_data4_i ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_data5  (.TRIEN(trien_cam_data5_i ), .DATA(out_cam_data5_i ), .RXEN(rxen_cam_data5_i ), .Y(in_cam_data5_o ), .PAD(pad_cam_data5 ), .PDEN(pd_cam_data5_i ), .PUEN(pu_cam_data5_i ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_data6  (.TRIEN(trien_cam_data6_i ), .DATA(out_cam_data6_i ), .RXEN(rxen_cam_data6_i ), .Y(in_cam_data6_o ), .PAD(pad_cam_data6 ), .PDEN(pd_cam_data6_i ), .PUEN(pu_cam_data6_i ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_data7  (.TRIEN(trien_cam_data7_i ), .DATA(out_cam_data7_i ), .RXEN(rxen_cam_data7_i ), .Y(in_cam_data7_o ), .PAD(pad_cam_data7 ), .PDEN(pd_cam_data7_i ), .PUEN(pu_cam_data7_i ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_cam_vsync  (.TRIEN(trien_cam_vsync_i ), .DATA(out_cam_vsync_i ), .RXEN(rxen_cam_vsync_i ), .Y(in_cam_vsync_o ), .PAD(pad_cam_vsync ), .PDEN(pd_cam_vsync_i ), .PUEN(pu_cam_vsync_i ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_spim_sck   (.TRIEN(trien_spim_sck_i  ), .DATA(out_spim_sck_i  ), .RXEN(rxen_spim_sck_i  ), .Y(in_spim_sck_o  ), .PAD(pad_spim_sck  ), .PDEN(pd_spim_sck_i  ), .PUEN(pu_spim_sck_i  ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_spim_sdio0 (.TRIEN(trien_spim_sdio0_i), .DATA(out_spim_sdio0_i), .RXEN(rxen_spim_sdio0_i), .Y(in_spim_sdio0_o), .PAD(pad_spim_sdio0), .PDEN(pd_spim_sdio0_i), .PUEN(pu_spim_sdio0_i), `DRV_SIG );

    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_uart_rx    (.TRIEN(trien_uart_rx_i   ), .DATA(out_uart_rx_i   ), .RXEN(rxen_uart_rx_i   ), .Y(in_uart_rx_o   ), .PAD(pad_uart_rx   ), .PDEN(pd_uart_rx_i   ), .PUEN(pu_uart_rx_i   ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_uart_tx    (.TRIEN(trien_uart_tx_i   ), .DATA(out_uart_tx_i   ), .RXEN(rxen_uart_tx_i   ), .Y(in_uart_tx_o   ), .PAD(pad_uart_tx   ), .PDEN(pd_uart_tx_i   ), .PUEN(pu_uart_tx_i   ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_i2c0_sda   (.TRIEN(trien_i2c0_sda_i  ), .DATA(out_i2c0_sda_i  ), .RXEN(rxen_i2c0_sda_i  ), .Y(in_i2c0_sda_o  ), .PAD(pad_i2c0_sda  ), .PDEN(pd_i2c0_sda_i  ), .PUEN(pu_i2c0_sda_i  ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V  padinst_i2c0_scl   (.TRIEN(trien_i2c0_scl_i  ), .DATA(out_i2c0_scl_i  ), .RXEN(rxen_i2c0_scl_i  ), .Y(in_i2c0_scl_o  ), .PAD(pad_i2c0_scl  ), .PDEN(pd_i2c0_scl_i  ), .PUEN(pu_i2c0_scl_i  ), `DRV_SIG );

    IN22FDX_GPIO18_10M3S30P_IO_V   padinst_reset_n   (.TRIEN(trien_reset_n_i   ), .DATA(                ), .RXEN(rxen_reset_n_i   ), .Y(rstn_o         ), .PAD(pad_reset_n   ), .PDEN(pd_reset_n_i   ), .PUEN(pu_reset_n_i   ), `DRV_SIG );
    IN22FDX_GPIO18_10M3S30P_IO_V   padinst_ref_clk   (.TRIEN(trien_ref_clk_i   ), .DATA(                ), .RXEN(rxen_ref_clk_i   ), .Y(ref_clk_o      ), .PAD(pad_xtal_in   ), .PDEN(pd_ref_clk_i   ), .PUEN(pu_ref_clk_i   ), `DRV_SIG );

`endif
    // for driving the signals PWROK_S, IOPWROK_S, BIAS_S and RETC_S
    IN22FDX_GPIO18_10M3S30P_PWRDET_V  pad_pwrdet (.PWROKOUT(PWROK_S), .IOPWROKOUT(IOPWROK_S), .BIAS(BIAS_S), .RETCIN(1'b0), .RETCOUT(RETC_S) );

endmodule
