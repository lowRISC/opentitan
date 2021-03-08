// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//############################################################################
// *Name: ast
// *Module Description: Analog Sensors Top
//############################################################################

`include "prim_assert.sv"

module ast #(
  parameter int AdcChannels     = 2,
  parameter int AdcDataWidth    = 10,
  parameter int EntropyStreams  = 4,
  parameter int Ast2PadOutWidth = 16,  // TODO:final size
  parameter int Pad2AstInWidth  = 16,  // TODO:final size
  parameter int UsbCalibWidth   = 16   // TODO:final size
) (
  // tlul if
  input tlul_pkg::tl_h2d_t tl_i,              // TLUL H2D
  output tlul_pkg::tl_d2h_t tl_o,             // TLUL D2H

  // clocks / resets
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
  input ast_pkg::awire_t adc_a0_ai,           // ADC A0 Analog Input
  input ast_pkg::awire_t adc_a1_ai,           // ADC A1 Analog Input
  input [AdcChannels-1:0] adc_chnsel_i,       // ADC Channel Select
  output [AdcDataWidth-1:0] adc_d_o,          // ADC Digital (per channel)
  output adc_d_val_o,                         // ADC Digital Valid

  // rng (entropy source) interface
  input rng_en_i,                             // RNG Enable
  output logic rng_val_o,                     // RNG Valid
  output logic [EntropyStreams-1:0] rng_b_o,  // RNG Bit(s)

  // entropy distribution interface
  input edn_pkg::edn_rsp_t entropy_rsp_i,     // Entropy Response
  output edn_pkg::edn_req_t entropy_req_o,    // Entropy Request

  // active shild alert
  input ast_pkg::ast_dif_t as_alert_trig_i,   // Active Shield Alert Trigger
  input ast_pkg::ast_dif_t as_alert_ack_i,    // Active Shield Alert Acknowledge
  output ast_pkg::ast_dif_t as_alert_o,       // Active Shield Alert

  // clock glitch alert
  input ast_pkg::ast_dif_t cg_alert_trig_i,   // Clock Glitch Alert Trigger
  input ast_pkg::ast_dif_t cg_alert_ack_i,    // Clock Glitch Alert Acknowledge
  output ast_pkg::ast_dif_t cg_alert_o,       // Clock Glitch Alert

  // glitch detect alert
  input ast_pkg::ast_dif_t gd_alert_trig_i,   // Glitch Detect Alert Trigger
  input ast_pkg::ast_dif_t gd_alert_ack_i,    // Glitch Detect Alert Acknowledge
  output ast_pkg::ast_dif_t gd_alert_o,       // Glitch Detect Alert

  // temp sense high alert
  input ast_pkg::ast_dif_t ts_alert_hi_trig_i,  // Temp Sense High Alert Trigger
  input ast_pkg::ast_dif_t ts_alert_hi_ack_i,   // Temp Sense High Alert Acknowledge
  output ast_pkg::ast_dif_t ts_alert_hi_o,      // Temp Sense High Alert Positive

  // temp sense low alert
  input ast_pkg::ast_dif_t ts_alert_lo_trig_i,  // Temp Sense Low Alert Trigger
  input ast_pkg::ast_dif_t ts_alert_lo_ack_i,   // Temp Sense Low Alert Acknowledge
  output ast_pkg::ast_dif_t ts_alert_lo_o,      // Temp Sense Low Alert

  // light sense alert
  input ast_pkg::ast_dif_t ls_alert_trig_i,   // Light Sense Alert Trigger
  input ast_pkg::ast_dif_t ls_alert_ack_i,    // Light Sense Alert Acknowledge
  output ast_pkg::ast_dif_t ls_alert_o,       // Light Sense Alert

  // other alert
  input ast_pkg::ast_dif_t ot_alert_trig_i,   // OTher Alert Trigger
  input ast_pkg::ast_dif_t ot_alert_ack_i,    // OTher Alert Acknowledge
  output ast_pkg::ast_dif_t ot_alert_o,       // OTher Alert

  // dft interface
  input pinmux_pkg::dft_strap_test_req_t dft_strap_test_i,  // DFT Straps
  input lc_ctrl_pkg::lc_tx_t lc_dft_en_i,     // DFT enable (secure bus)

  // pad mux/pad related
  input [Pad2AstInWidth-1:0] padmux2ast_i,    // IO_2_DFT Input Signals
  output logic [Ast2PadOutWidth-1:0] ast2padmux_o,  // DFT_2_IO Output Signals

  input ast_pkg::awire_t pad2ast_t0_ai,       // PAD_2_AST Analog T0 Input Signal
  input ast_pkg::awire_t pad2ast_t1_ai,       // PAD_2_AST Analog T1 Input Signal
  output ast_pkg::awire_t ast2pad_t0_ao,      // AST_2_PAD Analog T0 Output Signal
  output ast_pkg::awire_t ast2pad_t1_ao,      // AST_2_PAD Analog T1 Output Signal

  // flash and otp clock
  input  lc_ctrl_pkg::lc_tx_t lc_clk_byp_req_i, // External clock mux override for OTP bootstrap
  output lc_ctrl_pkg::lc_tx_t lc_clk_byp_ack_o, // Switch clocks to External clock
  output lc_ctrl_pkg::lc_tx_t flash_bist_en_o,  // Flush BIST (TAP) Enable

  // memories read-write margins
  output ast_pkg::dpm_rm_t dpram_rmf_o,       // Dual Port RAM Read-write Margin Fast
  output ast_pkg::dpm_rm_t dpram_rml_o,       // Dual Port RAM Read-write Margin sLow
  output ast_pkg::spm_rm_t spram_rm_o,        // Single Port RAM Read-write Margin
  output ast_pkg::spm_rm_t sprgf_rm_o,        // Single Port Reg-File Read-write Margin
  output ast_pkg::spm_rm_t sprom_rm_o,        // Single Port ROM Read-write Margin

  // Scan interface
  output lc_ctrl_pkg::lc_tx_t dft_scan_md_o,  // Scan Mode output
  output scan_shift_en_o,                     // Scan Shift Enable output
  output scan_reset_no                        // Scan Reset output
);

import ast_pkg::* ;
import ast_reg_pkg::* ;
import ast_bhv_pkg::* ;

logic vcaon_pok, vcaon_pok_h, scan_mode, scan_reset_n;
assign scan_reset_n = scan_reset_no;



///////////////////////////////////////
// VCC POK (Always ON)
///////////////////////////////////////
logic vcc_pok_h, vcc_pok;

vcc_pok u_vcc_pok (
  .vcc_pok_o ( vcc_pok_int )
);  // of u_vcc_pok

assign vcc_pok = vcc_pok_int && vcc_supp_i;
assign vcc_pok_h = vcc_pok;     // "Level Shifter"


///////////////////////////////////////
// VCAON POK (Always ON)
///////////////////////////////////////
logic vcmain_pok, vcmain_pok_h, vcaon_pok_por;

logic vcaon_pok_h_int;

assign vcaon_pok_h = vcaon_pok_h_int && vcaon_supp_i;
assign vcaon_pok = vcaon_pok_h;  // Level Shifter

// 'por_sync_n' reset deasetion synchronizer output
logic por_rst_n, por_synco_n, por_sync_n;

assign por_rst_n = scan_mode ? scan_reset_n : por_ni && vcc_pok && vcaon_pok;
// Reset De-Assert Sync
prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_por_dasrt (
  .clk_i ( clk_src_aon_o ),
  .rst_ni ( por_rst_n ),
  .d_i ( 1'b1 ),
  .q_o ( por_synco_n )
);
assign por_sync_n = scan_mode ? scan_reset_n : por_synco_n;

assign vcaon_pok_por = por_sync_n && vcc_pok && vcaon_pok;
assign vcaon_pok_o   = vcaon_pok_por;


///////////////////////////////////////
// VCMAIN POK (Always ON)
///////////////////////////////////////
logic vcmain_pok_por;
// Power up/down with rise/fall delays.
logic vcmain_pok_int, main_pwr_dly_o;

vcmain_pok u_vcmain_pok (
  .vcmain_pok_o ( vcmain_pok_int )
);  // of u_vcmain_pok

assign vcmain_pok = vcmain_pok_int && vcmain_supp_i && main_pwr_dly_o ;
assign vcmain_pok_h = vcmain_pok;   // Level Shifter

// assign vcmain_pok_o = vcaon_pok_o && vcmain_pok && pwr_switch_done_i;
assign vcmain_pok_por = vcaon_pok_por && vcmain_pok;
assign vcmain_pok_o   = vcmain_pok_por;


///////////////////////////////////////
// VIOA POK (Always ON)
///////////////////////////////////////
logic vioa_pok;
logic vioa_pok_int;

vio_pok u_vioa_pok (
  .vio_pok_o ( vioa_pok_int )
);  // of u_vioa_pok

assign vioa_pok = vioa_pok_int && vioa_supp_i;

assign vioa_pok_o = vcaon_pok && vioa_pok;


///////////////////////////////////////
// VIOB POK (Always ON)
///////////////////////////////////////
logic viob_pok;
logic viob_pok_int;

vio_pok u_viob_pok (
  .vio_pok_o ( viob_pok_int )
);  // of u_viob_pok

assign viob_pok = viob_pok_int && viob_supp_i;

assign viob_pok_o = vcaon_pok && viob_pok;


///////////////////////////////////////
// Regulators & PDM Logic (VCC)
///////////////////////////////////////

rglts_pdm_3p3v u_rglts_pdm_3p3v (
  .vcc_pok_h_i ( vcc_pok_h ),
  .vcmain_pok_h_i ( vcmain_pok_h ),
  .vcmain_pok_o_h_i ( vcmain_pok_por ),
  .clk_src_aon_h_i ( clk_src_aon_o ),
  .main_pd_h_ni ( main_pd_ni ),
  .otp_power_seq_h_i ( otp_power_seq_i[1:0] ),
  .vcaon_pok_h_o ( vcaon_pok_h_int ),
  .main_pwr_dly_o ( main_pwr_dly_o ),
  .otp_power_seq_h_o ( otp_power_seq_h_o[1:0] ),
  .flash_power_down_h_o ( flash_power_down_h_o ),
  .flash_power_ready_h_o ( flash_power_ready_h_o )
);  // of u_rglts_pdm_3p3v


///////////////////////////////////////
// System Clock (Always ON)
///////////////////////////////////////
logic rst_sys_clk_n;
assign rst_sys_clk_n = vcmain_pok_por;  // Scna reset included

sys_clk u_sys_clk (
  .vcore_pok_h_i ( vcaon_pok_h ),
  .clk_sys_pd_ni ( vcmain_pok ),
  .rst_sys_clk_ni ( rst_sys_clk_n ),
  .clk_src_sys_en_i ( clk_src_sys_en_i ),
  .clk_src_sys_jen_i ( clk_src_sys_jen_i ),
  .clk_src_sys_o ( clk_src_sys_o ),
  .clk_src_sys_val_o ( clk_src_sys_val_o )
);  // of u_sys_clk


///////////////////////////////////////
// USB Clock (Always ON)
///////////////////////////////////////
logic rst_usb_clk_n;
assign rst_usb_clk_n = vcmain_pok_por;  // Scan reset included

usb_clk u_usb_clk (
  .vcore_pok_h_i ( vcaon_pok_h ),
  .clk_usb_pd_ni ( vcmain_pok ),
  .rst_usb_clk_ni ( rst_usb_clk_n ),
  .clk_src_usb_en_i ( clk_src_usb_en_i ),
  .usb_ref_val_i ( usb_ref_val_i ),
  .usb_ref_pulse_i ( usb_ref_pulse_i ),
  .clk_src_usb_o ( clk_src_usb_o ),
  .clk_src_usb_val_o ( clk_src_usb_val_o )
);  // of u_usb_clk


///////////////////////////////////////
// AON Clock (Always ON)
///////////////////////////////////////
logic rst_aon_clk_n;
 assign rst_aon_clk_n = vcaon_pok;

aon_clk  u_aon_clk (
  .vcore_pok_h_i ( vcaon_pok_h ),
  .clk_aon_pd_ni ( 1'b1 ),     // Always Enabled
  .rst_aon_clk_ni ( rst_aon_clk_n ),
  .clk_src_aon_en_i ( 1'b1 ),  // Always Enabled
  .clk_src_aon_o ( clk_src_aon_o ),
  .clk_src_aon_val_o ( clk_src_aon_val_o )
);  // of u_aon_clk


///////////////////////////////////////
// IO Clock (Always ON)
///////////////////////////////////////
logic rst_io_clk_n;
assign rst_io_clk_n = vcmain_pok_por;  // scan reset included

io_clk u_io_clk (
  .vcore_pok_h_i ( vcaon_pok_h ),
  .clk_io_pd_ni ( vcmain_pok ),
  .rst_io_clk_ni ( rst_io_clk_n ),
  .clk_src_io_en_i ( clk_src_io_en_i ),
  .clk_src_io_o ( clk_src_io_o ),
  .clk_src_io_val_o ( clk_src_io_val_o )
);  // of u_io_clk


///////////////////////////////////////
// ADC (Always ON)
///////////////////////////////////////
adc #(
  .AdcCnvtClks ( AdcCnvtClks ),
  .AdcChannels ( AdcChannels ),
  .AdcDataWidth ( AdcDataWidth )
) u_adc (
  .adc_a0_ai ( adc_a0_ai ),
  .adc_a1_ai ( adc_a1_ai ),
  .adc_chnsel_i ( adc_chnsel_i[AdcChannels-1:0] ),
  .adc_pd_i ( adc_pd_i ),
  .clk_adc_i ( clk_ast_adc_i ),
  .rst_adc_ni ( rst_ast_adc_ni ),
  .adc_d_o ( adc_d_o[AdcDataWidth-1:0] ),
  .adc_d_val_o ( adc_d_val_o )
);  // of u_adc


///////////////////////////////////////
// Entropy (Always ON)
///////////////////////////////////////
localparam int EntropyRateWidth = 4;
logic [EntropyRateWidth-1:0] entropy_rate_o;

assign entropy_rate_o = 4'd5;

ast_entropy #(
  .EntropyRateWidth ( EntropyRateWidth )
) u_entropy (
  .entropy_rsp_i ( entropy_rsp_i ),
  .entropy_rate_i ( entropy_rate_o[EntropyRateWidth-1:0] ),
  .clk_ast_es_i ( clk_ast_es_i ),
  .rst_ast_es_ni ( rst_ast_es_ni ),
  .clk_src_sys_en_i ( clk_src_sys_en_i ),
  .clk_src_sys_jen_i ( clk_src_sys_jen_i ),
  .scan_mode_i ( scan_mode ),
  .scan_reset_ni ( scan_reset_n ),
  .entropy_req_o ( entropy_req_o )
);  // of u_entropy


///////////////////////////////////////
// RNG (Always ON)
///////////////////////////////////////
rng #(
  .EntropyStreams ( EntropyStreams )
) u_rng (
  .clk_i ( clk_ast_rng_i ),
  .rst_ni ( rst_ast_rng_ni ),
  .vcaon_pok_i ( vcaon_pok ),
  .rng_en_i ( rng_en_i ),
  .scan_mode_i ( scan_mode ),
  .scan_reset_ni ( scan_reset_n ),
  .rng_b_o ( rng_b_o[EntropyStreams-1:0] ),
  .rng_val_o ( rng_val_o )
);  // of u_rng


///////////////////////////////////////
// Alerts (Always ON)
///////////////////////////////////////

// Active Shield (AS)
///////////////////////////////////////
ast_pkg::ast_dif_t as_alert_in;
assign as_alert_in = '{p: 1'b0, n: 1'b1};

ast_alert u_alert_as (
  .clk_i ( clk_ast_alert_i ),
  .rst_ni ( rst_ast_alert_ni ),
  .alert_in_i ( as_alert_in ),
  .alert_trig_i ( as_alert_trig_i ),
  .alert_ack_i ( as_alert_ack_i ),
  .alert_req_o ( as_alert_o )
);  // u_alert_as

// Clock Glitch (CG)
///////////////////////////////////////
ast_pkg::ast_dif_t cg_alert_in;
assign cg_alert_in = '{p: 1'b0, n: 1'b1};

ast_alert u_alert_cg (
  .clk_i ( clk_ast_alert_i ),
  .rst_ni ( rst_ast_alert_ni ),
  .alert_in_i ( cg_alert_in ),
  .alert_trig_i ( cg_alert_trig_i ),
  .alert_ack_i ( cg_alert_ack_i ),
  .alert_req_o ( cg_alert_o )
);  // of u_alert_cg

// Glitch Detector (GD)
///////////////////////////////////////
ast_pkg::ast_dif_t gd_alert_in;
assign gd_alert_in = '{p: 1'b0, n: 1'b1};

ast_alert u_alert_gd (
  .clk_i ( clk_ast_alert_i ),
  .rst_ni ( rst_ast_alert_ni ),
  .alert_in_i ( gd_alert_in ),
  .alert_trig_i ( gd_alert_trig_i ),
  .alert_ack_i ( gd_alert_ack_i ),
  .alert_req_o ( gd_alert_o )
);  // of u_alert_gd

// Temprature Sensor High (TS Hi)
///////////////////////////////////////
ast_pkg::ast_dif_t ts_alert_hi_in;
assign ts_alert_hi_in = '{p: 1'b0, n: 1'b1};

ast_alert u_alert_ts_hi (
  .clk_i ( clk_ast_alert_i ),
  .rst_ni ( rst_ast_alert_ni ),
  .alert_in_i ( ts_alert_hi_in ),
  .alert_trig_i ( ts_alert_hi_trig_i ),
  .alert_ack_i ( ts_alert_hi_ack_i ),
  .alert_req_o ( ts_alert_hi_o )
);  // of u_alert_ts_hi

// Temprature Sensor Low (TS Lo)
///////////////////////////////////////
ast_pkg::ast_dif_t ts_alert_lo_in;
assign ts_alert_lo_in = '{p: 1'b0, n: 1'b1};

ast_alert u_alert_ts_lo (
  .clk_i ( clk_ast_alert_i ),
  .rst_ni ( rst_ast_alert_ni ),
  .alert_in_i ( ts_alert_lo_in ),
  .alert_trig_i ( ts_alert_lo_trig_i ),
  .alert_ack_i ( ts_alert_lo_ack_i ),
  .alert_req_o ( ts_alert_lo_o )
);  // of u_alert_ts_lo

// Light Sensor (LS)
///////////////////////////////////////
ast_pkg::ast_dif_t ls_alert_in;
assign ls_alert_in = '{p: 1'b0, n: 1'b1};

ast_alert u_alert_ls (
  .clk_i ( clk_ast_alert_i ),
  .rst_ni ( rst_ast_alert_ni ),
  .alert_in_i ( ls_alert_in ),
  .alert_trig_i ( ls_alert_trig_i ),
  .alert_ack_i ( ls_alert_ack_i ),
  .alert_req_o ( ls_alert_o )
);  // of u_alert_ls

// Other Alert (OT)
///////////////////////////////////////
ast_pkg::ast_dif_t ot_alert_in;
assign ot_alert_in = '{p: 1'b0, n: 1'b1};

ast_alert u_alert_ot (
  .clk_i ( clk_ast_alert_i ),
  .rst_ni ( rst_ast_alert_ni ),
  .alert_in_i ( ot_alert_in ),
  .alert_trig_i ( ot_alert_trig_i ),
  .alert_ack_i ( ot_alert_ack_i ),
  .alert_req_o ( ot_alert_o )
); // of u_alert_ot


///////////////////////////////////////
// AST Registers (Always ON)
///////////////////////////////////////
ast_reg_pkg::ast_reg2hw_t reg2hw; // Write (To HW)
ast_reg_pkg::ast_hw2reg_t hw2reg; // Read  (From HW)

ast_reg_top u_reg (
  .clk_i ( clk_ast_tlul_i ),
  .rst_ni ( rst_ast_tlul_ni ),
  .tl_i ( tl_i ),
  .tl_o ( tl_o ),
  .reg2hw ( reg2hw ),
  .hw2reg ( hw2reg ),
  .devmode_i ( 1'b0 )
);  // u_reg

// Registers Output to AST
logic [32-1:0] ast_rwtype0_q;
logic [11-1:0] ast_rwtype1_q;

assign ast_rwtype0_q = reg2hw.rwtype0.q;
assign ast_rwtype1_q = { reg2hw.rwtype1.field15_8.q,
                         reg2hw.rwtype1.field4.q,
                         reg2hw.rwtype1.field1.q,
                         reg2hw.rwtype1.field0.q };

// AST to Registers Input
assign hw2reg.rwtype0.d  = 32'h0000_0000;
assign hw2reg.rwtype0.de = 1'b0;


///////////////////////////////////////
// DFT (Main | Always ON)
///////////////////////////////////////
//
assign usb_io_pu_cal_o  = {UsbCalibWidth{1'b0}};
//
assign ast2padmux_o   = {Ast2PadOutWidth{1'b0}};
assign ast2pad_t0_ao  = 0;
assign ast2pad_t1_ao  = 0;
//
assign lc_clk_byp_ack_o = lc_ctrl_pkg::Off;
assign flash_bist_en_o  = lc_ctrl_pkg::Off;
//
assign dpram_rmf_o      = 10'h000;
assign dpram_rml_o      = 10'h000;
assign spram_rm_o       = 5'h00;
assign sprgf_rm_o       = 5'h00;
assign sprom_rm_o       = 5'h00;
//
assign dft_scan_md_o    = lc_ctrl_pkg::Off;
assign scan_mode        = 1'b0;
assign scan_shift_en_o  = 1'b0;
assign scan_reset_no    = 1'b1;


////////////////
// Assertions //
////////////////

`ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid, clk_ast_tlul_i, rst_ast_tlul_ni)
`ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready, clk_ast_tlul_i, rst_ast_tlul_ni)
`ASSERT_KNOWN(VcaonPokKnownO_A, vcaon_pok_o, clk_src_aon_o, por_ni)                      //TODO
`ASSERT_KNOWN(VcmainPokKnownO_A, vcmain_pok_o, clk_src_aon_o, por_ni)                    //TODO
`ASSERT_KNOWN(VioaPokKnownO_A, vioa_pok_o, clk_src_aon_o, por_ni)                        //TODO
`ASSERT_KNOWN(ViobPokKnownO_A, viob_pok_o, clk_src_aon_o, por_ni)                        //TODO
`ASSERT_KNOWN(FlashPowerDownKnownO_A, flash_power_down_h_o, 1, vcmain_pok_o)             //TODO
`ASSERT_KNOWN(FlashPowerReadyKnownO_A, flash_power_ready_h_o, 1, vcmain_pok_o)           //TODO
`ASSERT_KNOWN(OtpPowerSeqKnownO_A, otp_power_seq_h_o, 1, vcmain_pok_o)                   //TODO
`ASSERT_KNOWN(ClkSrcSysKnownO_A, clk_src_sys_o, 1, vcmain_pok_o)                         //TODO
`ASSERT_KNOWN(ClkSrcSysValKnownO_A, clk_src_sys_val_o, clk_src_sys_o, vcmain_pok_o)
`ASSERT_KNOWN(ClkSrcAonKnownO_A, clk_src_aon_o, 1, vcaon_pok_o)                          //TODO
`ASSERT_KNOWN(ClkSrcAonValKnownO_A, clk_src_aon_val_o, clk_src_aon_o, vcaon_pok_o)
`ASSERT_KNOWN(ClkSrcIoKnownO_A, clk_src_io_o, 1, vcaon_pok_o)                            //TODO
`ASSERT_KNOWN(ClkSrcIoValKnownO_A, clk_src_io_val_o, clk_src_io_o, vcaon_pok_o)
`ASSERT_KNOWN(ClkSrcUsbKnownO_A, clk_src_usb_o, 1, vcmain_pok_o)                         //TODO
`ASSERT_KNOWN(ClkSrcUsbValKnownO_A, clk_src_usb_val_o, clk_src_usb_o, vcmain_pok_o)
`ASSERT_KNOWN(UsbIoPuCalKnownO_A, usb_io_pu_cal_o, clk_ast_tlul_i, rst_ast_tlul_ni)
`ASSERT_KNOWN(AdcDKnownO_A, adc_d_o, clk_ast_adc_i, rst_ast_adc_ni)
`ASSERT_KNOWN(AdcDValKnownO_A, adc_d_val_o, clk_ast_adc_i, rst_ast_adc_ni)
`ASSERT_KNOWN(RngValKnownO_A, rng_val_o, clk_ast_rng_i, rst_ast_rng_ni)
`ASSERT_KNOWN(RngBKnownO_A, rng_b_o, clk_ast_rng_i, rst_ast_rng_ni)
`ASSERT_KNOWN(EntropyRateKnownO_A, entropy_rate_o, clk_ast_es_i, rst_ast_es_ni)
`ASSERT_KNOWN(EntropyReeqKnownO_A, entropy_req_o, clk_ast_es_i, rst_ast_es_ni)
`ASSERT_KNOWN(AsAlertPKnownO_A, as_alert_o, clk_ast_alert_i, rst_ast_alert_ni)
`ASSERT_KNOWN(CgAlertPKnownO_A, cg_alert_o, clk_ast_alert_i, rst_ast_alert_ni)
`ASSERT_KNOWN(GdAlertPKnownO_A, gd_alert_o, clk_ast_alert_i, rst_ast_alert_ni)
`ASSERT_KNOWN(TsAlertHiPKnownO_A, ts_alert_hi_o, clk_ast_alert_i, rst_ast_alert_ni)
`ASSERT_KNOWN(TsAlertLoPKnownO_A, ts_alert_lo_o, clk_ast_alert_i, rst_ast_alert_ni)
`ASSERT_KNOWN(LsAlertPKnownO_A, ls_alert_o, clk_ast_alert_i, rst_ast_alert_ni)
`ASSERT_KNOWN(OtAlertPKnownO_A, ot_alert_o, clk_ast_alert_i, rst_ast_alert_ni)
`ASSERT_KNOWN(Ast2PadmuxKnownO_A, ast2padmux_o, clk_ast_tlul_i, rst_ast_tlul_ni)
`ASSERT_KNOWN(Ast2PadT0KnownO_A, ast2pad_t0_ao, clk_ast_tlul_i, rst_ast_tlul_ni)       // ANALOG
`ASSERT_KNOWN(Ast2PadT1KnownO_A, ast2pad_t1_ao, clk_ast_tlul_i, rst_ast_tlul_ni)       // ANALOG
`ASSERT_KNOWN(LcClkBypAckEnKnownO_A, lc_clk_byp_ack_o, clk_ast_tlul_i, rst_ast_tlul_ni)  //TODO
`ASSERT_KNOWN(FlashBistEnKnownO_A, flash_bist_en_o, clk_ast_tlul_i, rst_ast_tlul_ni)     //TODO
`ASSERT_KNOWN(DpramRmfKnownO_A, dpram_rmf_o, clk_ast_tlul_i, vcaon_pok_o)
`ASSERT_KNOWN(DpramRmlKnownO_A, dpram_rml_o, clk_ast_tlul_i, vcaon_pok_o)
`ASSERT_KNOWN(SpramRmKnownO_A, spram_rm_o, clk_ast_tlul_i, vcaon_pok_o)
`ASSERT_KNOWN(SprgfRmKnownO_A, sprgf_rm_o, clk_ast_tlul_i, vcaon_pok_o)
`ASSERT_KNOWN(SpromRmKnownO_A, sprom_rm_o, clk_ast_tlul_i, vcaon_pok_o)
`ASSERT_KNOWN(DftScanMdKnownO_A, dft_scan_md_o, clk_ast_tlul_i, vcaon_pok_o)
`ASSERT_KNOWN(ScanShiftEnKnownO_A, scan_shift_en_o, clk_ast_tlul_i, vcaon_pok_o)
`ASSERT_KNOWN(ScanResetKnownO_A, scan_reset_no, clk_ast_tlul_i, vcaon_pok_o)             //TODO)

endmodule : ast
