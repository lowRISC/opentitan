// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: ast
// *Module Description: Analog Sensors Top
//############################################################################
`timescale 1ns / 10ps

module ast
  import ana_pkg::*;
  import lc_ctrl_pkg::*;
#(
  parameter int EntropyStreams  = 4,
  parameter int AdcChannels     = 2,
  parameter int AdcDataWidth    = 10,
  parameter int Ast2PadOutWidth = 16,         // TBD
  parameter int Pad2AstInWidth  = 16,         // TBD
  parameter int UsbCalibWidth   = 16          // TBD
) (

  // tlul if
  input  tlul_pkg::tl_h2d_t tl_i,             // TLUL H2D
  output tlul_pkg::tl_d2h_t tl_o,             // TLUL D2H

  // LC TX if
  input lc_ctrl_pkg::lc_tx_t lc_root_clk_byp_i,  // External clock mux override for OTP bootstrap
  input lc_ctrl_pkg::lc_tx_t lc_dft_en_i,     // DFT enable

  // clocks / rests
  input clk_ast_adc_i,                        // Buffered AST ADC Clock
  input rst_ast_adc_ni,                       // Buffered AST ADC Reset
  input clk_ast_alert_i,                      // Buffered AST Alert Clock
  input rst_ast_alert_ni,                     // Buffered AST Alert Reset
  input clk_ast_es_i,                         // Buffered AST Entropy Source Clock
  input rst_ast_es_ni,                        // Buffered AST Entropy Source Reset
  input clk_ast_rng_i,                        // Buffered AST RNG Clock
  input rst_ast_rng_ni,                       // Buffered AST RNG Reset
  input clk_ast_tlul_i,                       // Buffered AST TLUL Clock
  input rst_ast_tlul_ni,                      // Buffered AST TLUL Reset
  input clk_ast_usb_i,                        // Buffered AST USB Clock
  input rst_ast_usb_ni,                       // Buffered AST USB Reset
  input clk_ast_ext_i,                        // Buffered AST External Clock
  input por_ni,                               // Power ON Reset

  // power OK control
  // In non-power aware DV environment, the <>_supp_i is for debug only!
  // POK signal follow this input.
  // In a power aware environment this signal should be connected to constant '1'
  input vcc_supp_i,                           // VCC Supply Test for OS FPGA
  input vcaon_supp_i,                         // VCAON Supply Test for OS FPGA
  input vcmain_supp_i,                        // VCMAIN Supply Test for OS FPGA
  input vioa_supp_i,                          // VIOA Rail Supply Test for OS FPGA
  input viob_supp_i,                          // VIOB Rail Supply Test for OS FPGA
  output logic vcaon_pok_o,                   // VCAON Power OK
  output logic vcmain_pok_o,                  // VCMAIN Power OK
  output logic vioa_pok_o,                    // VIOA Rail Power OK
  output logic viob_pok_o,                    // VIOB Rail Power OK

  // Power and IO pin connections
  input main_pd_ni,                           // MAIN Regulator Power Down
  input main_iso_en_i,                        // Isolation enable for main core power (VCMAIN).

  // power down monitor logic - flash/otp related
  output logic flash_power_down_h_o,          // Flash Power Down
  output logic flash_power_ready_h_o,         // Flash Power Ready
  input [1:0] otp_power_seq_i,                // MMR0,24 in (VDD)
  output logic [1:0] otp_power_seq_h_o,       // MMR0,24 masked by PDM, out (VCC)

  // system source clock
  input clk_src_sys_en_i,                     // SYS Source Clock Enable
  input clk_src_sys_jen_i,                    // SYS Source Clock Jitter Enable
  output logic clk_src_sys_o,                 // SYS Source Clock
  output logic clk_src_sys_val_o,             // SYS Source Clock Valid

  // aon source clock
  output logic clk_src_aon_o,                 // AON Source Clock
  output logic clk_src_aon_val_o,             // AON Source Clock Valid

  // io source clock
  input clk_src_io_en_i,                      // IO Source Clock Enable
  output logic clk_src_io_o,                  // IO Source Clock
  output logic clk_src_io_val_o,              // IO Source Clock Valid

  // usb source clock
  input usb_ref_pulse_i,                      // USB Reference Pulse
  input usb_ref_val_i,                        // USB Reference Valid
  input clk_src_usb_en_i,                     // USB Source Clock Enable
  output logic clk_src_usb_o,                 // USB Source Clock
  output logic clk_src_usb_val_o,             // USB Source Clock Valid
  output logic [UsbCalibWidth-1:0] usb_io_pu_cal_o,  // USB IO Pull-up Calibration Setting

  // adc interface
  input adc_pd_i,                             // ADC Power Down
`ifndef VERILATOR
`ifndef SYNTHESIS
  input awire adc_a0_ai,                      // ADC A0 Analog Input
  input awire adc_a1_ai,                      // ADC A1 Analog Input
`else
  input wire adc_a0_ai,                       // ADC A0 Analog Input
  input wire adc_a1_ai,                       // ADC A1 Analog Input
`endif
`else
  input wire adc_a0_ai,                       // ADC A0 Analog Input
  input wire adc_a1_ai,                       // ADC A1 Analog Input
`endif
  input [AdcChannels-1:0] adc_chnsel_i,       // ADC Channel Select
  output [AdcDataWidth-1:0] adc_d_o,          // ADC Digital (per channel)
  output adc_d_val_o,                         // ADC Digital Valid

  // entropy source interface
  input rng_en_i,                             // RNG Enable
  output logic rng_val_o,                     // RNG Valid
  output logic [EntropyStreams-1:0] rng_b_o,  // RNG Bit(s)

  // entropy distribution interface
  input entropy_ack_i,                        // Entropy Acknowlage
  input entropy_i,                            // Entropy
  output logic entropy_req_o,                 // Entropy Request

  // alerts
  input as_alert_trig_i,                      // Active Shield Alert Trigger
  input as_alert_ack_i,                       // Active Shield Alert Acknowlage
  output logic as_alert_po,                   // Active Shield Alert Positive
  output logic as_alert_no,                   // Active Shield Alert Negative

  input cg_alert_trig_i,                      // CG Alert Trigger
  input cg_alert_ack_i,                       // CG Alert Acknowlage
  output logic cg_alert_po,                   // CG Alert Positive
  output logic cg_alert_no,                   // CG Alert Negative

  input gd_alert_trig_i,                      // GD Alert Trigger
  input gd_alert_ack_i,                       // GD Alert Acknowlage
  output logic gd_alert_po,                   // GD Alert Positive
  output logic gd_alert_no,                   // GD Alert Negative

  input ts_alert_hi_trig_i,                   // TS High Alert Trigger
  input ts_alert_hi_ack_i,                    // TS High Alert Acknowlage
  output logic ts_alert_hi_po,                // TS High Alert Positive
  output logic ts_alert_hi_no,                // TS High Alert Negative

  input ts_alert_lo_trig_i,                   // TS Low Alert Trigger
  input ts_alert_lo_ack_i,                    // TS Low Alert Acknowlage
  output logic ts_alert_lo_po,                // TS Low Alert Positive
  output logic ts_alert_lo_no,                // TS Low Alert Negative

  input ls_alert_trig_i,                      // LS Alert Trigger
  input ls_alert_ack_i,                       // LS Alert Acknowlage
  output logic ls_alert_po,                   // LS Alert Positive
  output logic ls_alert_no,                   // LS Alert Negative

  input ot_alert_trig_i,                      // OT Alert Trigger
  input ot_alert_ack_i,                       // OT Alert Acknowlage
  output logic ot_alert_po,                   // OT Alert Positive
  output logic ot_alert_no,                   // OT Alert Negative

  // pad mux related - DFT
  input [Pad2AstInWidth-1:0] padmux2ast_i,    // IO_2_DFT Input Signals
  output logic [Ast2PadOutWidth-1:0] ast2padmux_o,   // DFT_2_IO Output Signals
  inout wire ast2pad_a_io,                    // TODO: If needed, add width param

  // Scan
  input scan_mode_i,                          // Scan Mode
  input scan_reset_ni                         // Scan Reset
);

import ast_pkg::*;
import ast_reg_pkg::*;

logic vcaon_pok, vcaon_pok_h;



/////////////////////////////////
// Power OK
/////////////////////////////////

// VCC POK
logic vcc_pok_h, vcc_pok;
gen_pok #(
`ifndef VERILATOR
// synopsys translate_off
/*P*/ .POK_RDLY ( VCC_POK_RDLY ),
/*P*/ .POK_FDLY ( VCC_POK_FDLY )
// synopsys translate_on
`endif
) i_vcc_pok (
/*O*/ .gen_pok_o ( vcc_pok_int )
);

assign vcc_pok = vcc_pok_int && vcc_supp_i;
assign vcc_pok_h = vcc_pok;     // "Level Shifter"


// VCAON POK
logic vcmain_pok, vcmain_pok_h;
logic vcaon_pok_int, vcaon_pok_int_h;
assign vcaon_pok   = vcaon_pok_int && vcaon_supp_i;
assign vcaon_pok_h = vcaon_pok_int_h && vcaon_supp_i;

// 'por_sync_n' reset deasetion synchronizer output
logic por_syn_rst_n, por_sync0_n, por_sync_n;

assign por_syn_rst_n = por_ni && vcc_pok && vcaon_pok;

always_ff @( posedge clk_src_aon_o, negedge por_syn_rst_n ) begin
  if ( !por_syn_rst_n ) begin
    por_sync0_n <= 1'b0;
    por_sync_n  <= 1'b0;
  end
  else begin
    por_sync0_n <= 1'b1;
    por_sync_n  <= por_sync0_n;
  end
end

assign vcaon_pok_o = por_sync_n && vcc_pok && vcaon_pok;


// VCMAIN POK
// Power up/down with rise/fall delays.
logic vcmain_pok_int, main_pwr_dly_o;

gen_pok #(
`ifndef VERILATOR
// synopsys translate_off
/*P*/ .POK_RDLY ( VCMAIN_POK_RDLY ),
/*P*/ .POK_FDLY ( VCMAIN_POK_FDLY )
// synopsys translate_on
`endif
) i_vcmain_pok (
/*O*/ .gen_pok_o ( vcmain_pok_int )
);

assign vcmain_pok = vcmain_pok_int && vcmain_supp_i && main_pwr_dly_o ;
assign vcmain_pok_h = vcmain_pok;   // Level Shifter
assign vcmain_pok_o = vcaon_pok_o && vcmain_pok;


// VIOA POK
logic vioa_pok;
logic vioa_pok_int;

gen_pok #(
`ifndef VERILATOR
// synopsys translate_off
/*P*/ .POK_RDLY ( VIOA_POK_RDLY ),
/*P*/ .POK_FDLY ( VIOA_POK_FDLY )
// synopsys translate_on
`endif
) i_vioa_pok (
/*O*/ .gen_pok_o ( vioa_pok_int )
);

assign vioa_pok = vioa_pok_int && vioa_supp_i;

assign vioa_pok_o = vcaon_pok && vioa_pok;


// VIOB POK
logic viob_pok;
logic viob_pok_int;

gen_pok #(
`ifndef VERILATOR
// synopsys translate_off
/*P*/ .POK_RDLY ( VIOB_POK_RDLY ),
/*P*/ .POK_FDLY ( VIOB_POK_FDLY )
// synopsys translate_on
`endif
) i_viob_pok (
/*O*/ .gen_pok_o ( viob_pok_int )
);

assign viob_pok = viob_pok_int && viob_supp_i;

assign viob_pok_o = vcaon_pok && viob_pok;


/////////////////////////////////
// Regulators & PDM Logic
/////////////////////////////////

// Regulators (VCC)
// Analog & Digital are 3.3v
rglts_pdm_3p3v #(
`ifndef VERILATOR
// synopsys translate_off
/*P*/ .MRVCC_RDLY ( MPVCC_RDLY ),
/*P*/ .MRVCC_FDLY ( MPVCC_FDLY ),
/*P*/ .MRPD_RDLY ( MPPD_RDLY ),
/*P*/ .MRPD_FDLY ( MPPD_FDLY )
// synopsys translate_on
`endif
) i_rglts_pdm_3p3v (
/*I*/ .vcc_pok_h_i ( vcc_pok_h ),
/*I*/ .vcmain_pok_h_i ( vcmain_pok_h ),
/*I*/ .clk_src_aon_i ( clk_src_aon_o ),
/*I*/ .main_pd_ni ( main_pd_ni ),
/*I*/ .otp_power_seq_i ( otp_power_seq_i[1:0] ),
/*O*/ .main_pwr_dly_o ( main_pwr_dly_o ),
/*O*/ .vcaon_pok_o ( vcaon_pok_int ),
/*O*/ .vcaon_pok_h_o ( vcaon_pok_int_h ),
/*O*/ .otp_power_seq_h_o ( otp_power_seq_h_o[1:0] ),
/*O*/ .flash_power_down_h_o ( flash_power_down_h_o ),
/*O*/ .flash_power_ready_h_o ( flash_power_ready_h_o )
);


/////////////////////////////////
// Clocking
/////////////////////////////////

// System Clock (Always ON)
sys_clk #(
`ifndef VERILATOR
// synopsys translate_off
/*P*/ .SYS_EN_RDLY ( SYS_EN_RDLY )
// synopsys translate_on
`endif
) i_sys_clk (
/*I*/ .vcmain_pok_i ( vcmain_pok ),
/*I*/ .clk_src_sys_en_i ( clk_src_sys_en_i ),
/*I*/ .clk_src_sys_jen_i ( clk_src_sys_jen_i ),
/*O*/ .clk_src_sys_o ( clk_src_sys_o ),
/*O*/ .clk_src_sys_val_o ( clk_src_sys_val_o )
);

// USB Clock (Always ON)
usb_clk #(
`ifndef VERILATOR
// synopsys translate_off
/*P*/ .USB_EN_RDLY ( USB_EN_RDLY ),
/*P*/ .USB_VAL_RDLY ( USB_VAL_RDLY ),
/*P*/ .USB_VAL_FDLY ( USB_VAL_FDLY )
// synopsys translate_on
`endif
) i_usb_clk (
/*I*/ .vcmain_pok_i ( vcmain_pok ),
/*I*/ .clk_src_usb_en_i ( clk_src_usb_en_i ),
/*I*/ .usb_ref_pulse_i ( usb_ref_pulse_i ),
/*I*/ .usb_ref_val_i ( usb_ref_val_i ),
/*O*/ .clk_src_usb_o ( clk_src_usb_o ),
/*O*/ .clk_src_usb_val_o ( clk_src_usb_val_o )
);

// AON Clock (Always ON)
aon_clk #(
`ifndef VERILATOR
// synopsys translate_off
/*P*/ .AON_EN_RDLY ( AON_EN_RDLY )
// synopsys translate_on
`endif
) i_aon_clk (
/*I*/ .vcaon_pok_i ( vcaon_pok ),
/*O*/ .clk_src_aon_o ( clk_src_aon_o ),
/*O*/ .clk_src_aon_val_o ( clk_src_aon_val_o )
);

// IO Clock (Always ON)
io_clk #(
`ifndef VERILATOR
// synopsys translate_off
/*P*/ .IO_EN_RDLY ( 5us )
// synopsys translate_on
`endif
) i_io_clk (
/*I*/ .vcmain_pok_i ( vcmain_pok ),
/*I*/ .clk_src_io_en_i ( clk_src_io_en_i ),
/*O*/ .clk_src_io_o ( clk_src_io_o ),
/*O*/ .clk_src_io_val_o ( clk_src_io_val_o )
);


/////////////////////////////////
// ADC
/////////////////////////////////

// ADC (Always ON)
adc #(
/*P*/ .AdcCnvtClks ( AdcCnvtClks ),
/*P*/ .AdcDataWidth ( AdcDataWidth ),
/*P*/ .AdcChannels ( AdcChannels )
) i_adc (
/*I*/ .adc_a0_ai ( adc_a0_ai ),
/*I*/ .adc_a1_ai ( adc_a1_ai ),
/*I*/ .adc_chnsel_i ( adc_chnsel_i[AdcChannels-1:0] ),
/*I*/ .adc_pd_i ( adc_pd_i ),
/*I*/ .clk_adc_i ( clk_ast_adc_i ),
/*I*/ .rst_adc_ni ( rst_ast_adc_ni ),
/*O*/ .adc_d_o ( adc_d_o[AdcDataWidth-1:0] ),
/*O*/ .adc_d_val_o ( adc_d_val_o )
);


/////////////////////////////////
// ENTROPY & RNG
/////////////////////////////////

// Entropy (Always ON)
localparam int EntropyRateWidth = 4;
logic [EntropyRateWidth-1:0] entropy_rate_o;

entropy #(
/*P*/ .EntropyRateWidth ( EntropyRateWidth )
) i_entropy (
/*I*/ .entropy_ack_i ( entropy_ack_i ),
/*I*/ .entropy_i ( entropy_i ),
/*I*/ .entropy_rate_i ( entropy_rate_o[EntropyRateWidth-1:0] ),
/*I*/ .clk_src_sys_jen_i ( clk_src_sys_jen_i ),
/*I*/ .clk_ast_es_i ( clk_ast_es_i ),
/*I*/ .rst_ast_es_ni ( rst_ast_es_ni ),
/*I*/ .clk_src_sys_i ( clk_src_sys_o ),
/*I*/ .rst_src_sys_ni ( vcmain_pok_o ),
/*I*/ .scan_mode_i ( scan_mode_i ),
/*O*/ .entropy_req_o ( entropy_req_o )
);

// RNG (Always ON)
rng #(
`ifndef VERILATOR
// synopsys translate_off
/*P*/ .RNG_EN_RDLY ( RNG_EN_RDLY ),
// synopsys translate_on
`endif
/*P*/ .EntropyStreams ( EntropyStreams )
) i_rng (
/*I*/ .clk_i ( clk_ast_rng_i ),
/*I*/ .rst_ni ( rst_ast_rng_ni ),
/*I*/ .vcaon_pok_i ( vcaon_pok ),
/*I*/ .rng_en_i ( rng_en_i ),
/*O*/ .rng_b_o ( rng_b_o[EntropyStreams-1:0] ),
/*O*/ .rng_val_o ( rng_val_o )
);


//////////////////////////////////
// Alerts (Always ON)
/////////////////////////////////

// Active Shield (AS)
gen_alert i_alert_as (
/*I*/ .clk_i ( clk_ast_alert_i ),
/*I*/ .rst_ni ( rst_ast_alert_ni ),
/*I*/ .gen_alert_trig_i ( as_alert_trig_i ),
/*I*/ .gen_alert_ack_i ( as_alert_ack_i ),
/*O*/ .gen_alert_po ( as_alert_po ),
/*O*/ .gen_alert_no ( as_alert_no )
);

// Clock Glitch (CG)
gen_alert i_alert_cg (
/*I*/ .clk_i ( clk_ast_alert_i ),
/*I*/ .rst_ni ( rst_ast_alert_ni ),
/*I*/ .gen_alert_trig_i ( cg_alert_trig_i ),
/*I*/ .gen_alert_ack_i ( cg_alert_ack_i ),
/*O*/ .gen_alert_po ( cg_alert_po ),
/*O*/ .gen_alert_no ( cg_alert_no )
);

// Glitch Detector (GD)
gen_alert i_alert_gd (
/*I*/ .clk_i ( clk_ast_alert_i ),
/*I*/ .rst_ni ( rst_ast_alert_ni ),
/*I*/ .gen_alert_trig_i ( gd_alert_trig_i ),
/*I*/ .gen_alert_ack_i ( gd_alert_ack_i ),
/*O*/ .gen_alert_po ( gd_alert_po ),
/*O*/ .gen_alert_no ( gd_alert_no )
);

// Temprature Sensor High (TS Hi)
gen_alert i_alert_ts_hi (
/*I*/ .clk_i ( clk_ast_alert_i ),
/*I*/ .rst_ni ( rst_ast_alert_ni ),
/*I*/ .gen_alert_trig_i ( ts_alert_hi_trig_i ),
/*I*/ .gen_alert_ack_i ( ts_alert_hi_ack_i ),
/*O*/ .gen_alert_po ( ts_alert_hi_po ),
/*O*/ .gen_alert_no ( ts_alert_hi_no )
);

// Temprature Sensor Low (TS Lo)
gen_alert i_alert_ts_lo (
/*I*/ .clk_i ( clk_ast_alert_i ),
/*I*/ .rst_ni ( rst_ast_alert_ni ),
/*I*/ .gen_alert_trig_i ( ts_alert_lo_trig_i ),
/*I*/ .gen_alert_ack_i ( ts_alert_lo_ack_i ),
/*O*/ .gen_alert_po ( ts_alert_lo_po ),
/*O*/ .gen_alert_no ( ts_alert_lo_no )
);

// Light Sensor (LS)
gen_alert i_alert_ls (
/*I*/ .clk_i ( clk_ast_alert_i ),
/*I*/ .rst_ni ( rst_ast_alert_ni ),
/*I*/ .gen_alert_trig_i ( ls_alert_trig_i ),
/*I*/ .gen_alert_ack_i ( ls_alert_ack_i ),
/*O*/ .gen_alert_po ( ls_alert_po ),
/*O*/ .gen_alert_no ( ls_alert_no )
);

// Other Alert (OT)
gen_alert i_alert_ot (
/*I*/ .clk_i ( clk_ast_alert_i ),
/*I*/ .rst_ni ( rst_ast_alert_ni ),
/*I*/ .gen_alert_trig_i ( ot_alert_trig_i ),
/*I*/ .gen_alert_ack_i ( ot_alert_ack_i ),
/*O*/ .gen_alert_po ( ot_alert_po ),
/*O*/ .gen_alert_no ( ot_alert_no )
);


/////////////////////////////////
// AST Registers Top
/////////////////////////////////

// AST REGs (Always ON)
ast_reg_pkg::ast_reg2hw_t reg2hw; // Write (To HW)
ast_reg_pkg::ast_hw2reg_t hw2reg; // Read  (From HW)

ast_reg_top i_ast_reg_top (
/*I*/ .clk_i ( clk_ast_tlul_i ),
/*I*/ .rst_ni ( rst_ast_tlul_ni ),
/*I*/ .tl_i ( tl_i ),
/*O*/ .tl_o ( tl_o ),
/*O*/ .reg2hw ( reg2hw ),
/*I*/ .hw2reg ( hw2reg ),
/*I*/ .devmode_i ( 1'b0 )
);

// Registers Output to AST
logic [32-1:0] ast_rwtype0_q;
logic [11-1:0] ast_rwtype1_q;

assign ast_rwtype0_q = reg2hw.rwtype0.q;
assign ast_rwtype1_q = { reg2hw.rwtype1.field15_8.q,
                         reg2hw.rwtype1.field4.q,
                         reg2hw.rwtype1.field1.q,
                         reg2hw.rwtype1.field0.q };

// AST to Registers Input
assign hw2reg.rwtype0.d = 32'h0000_0000;
assign hw2reg.rwtype0.de = 1'b0;


///////////////////////////////////////
// DFT to PADs / PADs to DFT
///////////////////////////////////////
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
// TODO: Temporrary assignment
//~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
assign entropy_rate_o = 4'd5;
assign usb_io_pu_cal_o = {UsbCalibWidth{1'b0}};  // From AST Regfile

assign ast2padmux_o = {Ast2PadOutWidth{1'b0}};   // DFT from AST Analog/Digital


endmodule // of ast
