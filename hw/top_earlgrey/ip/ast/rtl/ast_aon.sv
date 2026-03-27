// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// -------- W A R N I N G: A U T O - G E N E R A T E D  C O D E !! -------- //
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED (by closed source generator).
//
//############################################################################
// *Name: ast
// *Module Description: Analog Sensors Top
//############################################################################

`include "prim_assert.sv"

module ast_aon (
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

  // sensed clocks / resets
  input clkmgr_pkg::clkmgr_out_t sns_clks_i,  // Sensed Clocks
  input rstmgr_pkg::rstmgr_out_t sns_rsts_i,  // Sensed Resets
  input sns_spi_ext_clk_i,                    // Sensed SPI External Clock

`ifdef AST_BYPASS_CLK
  // Clocks' Oschillator bypass for OS FPGA
  input ast_pkg::clks_osc_byp_t clk_osc_byp_i,  // Clocks' Oschillator bypass for OS FPGA/VERILATOR
`endif

  // power OK control
  // In non-power aware DV environment, the <>_supp_i is for debug only!
  // POK signal follow this input.
  // In a power aware environment this signal should be connected to constant '1'
  input vcc_supp_i,                           // VCC Supply Test for OS FPGA
  input vcaon_supp_i,                         // VCAON Supply Test for OS FPGA
  input vcmain_supp_i,                        // VCMAIN Supply Test for OS FPGA
  input vioa_supp_i,                          // VIOA Rail Supply Test for OS FPGA
  input viob_supp_i,                          // VIOB Rail Supply Test for OS FPGA
  output ast_pkg::ast_pwst_t ast_pwst_o,      // AON, MAIN, IO-0 Rail, IO-1 Rail Power OK @1.1V
  output ast_pkg::ast_pwst_t ast_pwst_h_o,    // AON, MAIN, IO-9 Rail, IO-1 Rail Power OK @3.3V

  // Power and IO pin connections
  input main_pd_ni,                           // MAIN Regulator Power Down
  input main_env_iso_en_i,                    // Enveloped ISOlation ENable for MAIN

  // power down monitor logic - flash/otp related
  output logic flash_power_down_h_o,          // Flash Power Down
  output logic flash_power_ready_h_o,         // Flash Power Ready
  input [1:0] otp_power_seq_i,                // MMR0,24 in (VDD)
  output logic [1:0] otp_power_seq_h_o,       // MMR0,24 masked by PDM, out (VCC)

  // aon source clock
  output logic clk_src_aon_o,                 // AON Source Clock
  output logic clk_src_aon_val_o,             // AON Source Clock Valid

  // USB reference and calibration (clock outputs moved to ast_main)
  input usb_ref_pulse_i,                      // USB Reference Pulse
  input usb_ref_val_i,                        // USB Reference Valid
  input clk_src_usb_en_i,                     // USB Source Clock Enable
  output logic [ast_pkg::UsbCalibWidth-1:0] usb_io_pu_cal_o,  // USB IO Pull-up Calibration Setting

  // adc interface
  input adc_pd_i,                             // ADC Power Down
  input ast_pkg::awire_t adc_a0_ai,           // ADC A0 Analog Input
  input ast_pkg::awire_t adc_a1_ai,           // ADC A1 Analog Input
  input [ast_pkg::AdcChannels-1:0] adc_chnsel_i,       // ADC Channel Select
  output [ast_pkg::AdcDataWidth-1:0] adc_d_o,          // ADC Digital (per channel)
  output adc_d_val_o,                         // ADC Digital Valid

  // alerts
  input ast_pkg::ast_alert_rsp_t alert_rsp_i,  // Alerts Trigger & Acknowledge Inputs
  output ast_pkg::ast_alert_req_t alert_req_o, // Alerts Output

  // dft interface
  input pinmux_pkg::dft_strap_test_req_t dft_strap_test_i,  // DFT Straps
  input lc_ctrl_pkg::lc_tx_t lc_dft_en_i,     // DFT enable (secure bus)
  input [8-1:0] fla_obs_i,                    // FLASH Observe Bus
  input [8-1:0] otp_obs_i,                    // OTP Observe Bus
  input [8-1:0] otm_obs_i,                    // OT Modules Observe Bus
  input usb_obs_i,                            // USB DIFF RX Observe
  output ast_pkg::ast_obs_ctrl_t obs_ctrl_o,  // Observe Control

  // pad mux/pad related
  input [ast_pkg::Pad2AstInWidth-1:0] padmux2ast_i,    // IO_2_DFT Input Signals
  output logic [ast_pkg::Ast2PadOutWidth-1:0] ast2padmux_o,  // DFT_2_IO Output Signals
  output logic [4-1:0] mux_iob_sel_o, // iob or spi selector

`ifdef ANALOGSIM
  output real ast2pad_t0_ao,                  // AST_2_PAD Analog T0 Output Signal
  output real ast2pad_t1_ao,                  // AST_2_PAD Analog T1 Output Signal
`else
  output wire ast2pad_t0_ao,                  // AST_2_PAD Analog T0 Output Signal
  output wire ast2pad_t1_ao,                  // AST_2_PAD Analog T1 Output Signal
`endif

  // flash and external clocks (clock bypass acks moved to ast_main)
  input prim_mubi_pkg::mubi4_t ext_freq_is_96m_i,   // External clock frequecy is 96MHz
  input prim_mubi_pkg::mubi4_t all_clk_byp_req_i,   // All clocks bypass request
  input prim_mubi_pkg::mubi4_t io_clk_byp_req_i,    // IO clock bypass request
  output prim_mubi_pkg::mubi4_t flash_bist_en_o,    // Flush BIST (TAP) Enable

  // memories read-write margins
  output ast_pkg::dpm_rm_t dpram_rmf_o,       // Dual Port RAM Read-write Margin Fast
  output ast_pkg::dpm_rm_t dpram_rml_o,       // Dual Port RAM Read-write Margin sLow
  output ast_pkg::spm_rm_t spram_rm_o,        // Single Port RAM Read-write Margin
  output ast_pkg::spm_rm_t sprgf_rm_o,        // Single Port Reg-File Read-write Margin
  output ast_pkg::spm_rm_t sprom_rm_o,        // Single Port ROM Read-write Margin

  // Scan interface
  output prim_mubi_pkg::mubi4_t dft_scan_md_o,  // Scan Mode output
  output scan_shift_en_o,                       // Scan Shift Enable output
  output scan_reset_no,                          // Scan Reset output

  // Inter-domain communication
  output ast_aon_main_pkg::aon_to_main_t aon_to_main_o,
  input ast_aon_main_pkg::main_to_aon_t main_to_aon_i
);

import ast_pkg::* ;
import ast_reg_pkg::* ;
import ast_aon_main_pkg::* ;
import ast_bhv_pkg::* ;

///////////////////////////////////////
// Inter-domain Interface Unpacking (OS simplified)
///////////////////////////////////////
ast_aon_main_pkg::clks_byp_main_to_aon_t clks_byp_main_to_aon;
assign clks_byp_main_to_aon = main_to_aon_i.clks_byp;

logic scan_mode, shift_en, scan_reset_n;
logic vcc_pok, vcc_pok_h, vcc_pok_str;
logic vcaon_pok, vcaon_pok_h, vcmain_pok_h;
logic vcaon_pok_por, vcmain_pok_por;

// Local (AST) AON clock buffer
////////////////////////////////////////
logic clk_aon;

prim_clock_buf #(
  .NoFpgaBuf ( 1'b1 )
) u_clk_aon_buf (
  .clk_i ( clk_src_aon_o ),
  .clk_o ( clk_aon )
);

assign flash_bist_en_o  = prim_mubi_pkg::MuBi4False;
assign dft_scan_md_o    = prim_mubi_pkg::MuBi4False;
assign scan_shift_en_o  = 1'b0;
assign scan_reset_no    = 1'b1;
assign scan_mode        = 1'b0;
assign shift_en         = 1'b0;
assign scan_reset_n     = 1'b1;

///////////////////////////////////////
// VCC POK (Always ON)
///////////////////////////////////////
logic vcc_pok_int;

vcc_pgd u_vcc_pok (
  .vcc_pok_o ( vcc_pok_int )
);

assign vcc_pok = vcc_pok_int && vcc_supp_i;
assign vcc_pok_h = vcc_pok;     // "Level Shifter"


////////////////////////////////////////
// VCAON POK POR (Always ON)
///////////////////////////////////////
logic rst_poks_n, rst_poks_por_n, por_sync_n;
logic vcaon_pok_por_src, vcaon_pok_por_lat, poks_por_ack, rglssm_vcmon, rglssm_brout;

assign rst_poks_n = vcc_pok_str && vcaon_pok;
assign rst_poks_por_n = vcc_pok_str && vcaon_pok && por_ni;
assign poks_por_ack = vcaon_pok_por_src || rglssm_vcmon;

// Reset De-Assert Sync
prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_no_scan_poks_por_dasrt (
  .clk_i ( clk_aon ),
  .rst_ni ( rst_poks_por_n ),
  .d_i ( poks_por_ack ),
  .q_o ( vcaon_pok_por_src )
);

logic clk_aon_n;

prim_clock_inv #(
  .HasScanMode ( 1 )
) u_clk_aon_inv (
  .clk_i ( clk_aon ),
  .scanmode_i ( scan_mode ),
  .clk_no ( clk_aon_n )
);

prim_flop #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_no_scan_por_sync_n (
  .clk_i ( clk_aon_n ),
  .rst_ni ( rst_poks_n ),
  .d_i ( vcaon_pok_por_src ),
  .q_o ( por_sync_n )
);

// Replace Latch for the OS code
assign vcaon_pok_por_lat = rglssm_brout || por_sync_n;
assign vcaon_pok_por = scan_mode ? scan_reset_n : vcaon_pok_por_lat;
assign ast_pwst_o.aon_pok = vcaon_pok_por;

////////////////////////////////////////
// VCMAIN POK POR (Always ON)
///////////////////////////////////////
logic rglssm_vmppr, vcmain_pok_por_src;

assign vcmain_pok_por_src = vcaon_pok_por_lat && vcmain_pok_h && !rglssm_vmppr;
assign vcmain_pok_por = scan_mode ? scan_reset_n : vcmain_pok_por_src;
assign ast_pwst_o.main_pok = vcmain_pok_por;

///////////////////////////////////////
// VIOA POK (Always ON)
///////////////////////////////////////
logic vioa_pok;
logic vioa_pok_int;

vio_pgd u_vioa_pok (
  .vio_pok_o ( vioa_pok_int )
);

assign vioa_pok = vioa_pok_int && vioa_supp_i;
assign ast_pwst_o.io_pok[0] = vcaon_pok && vioa_pok;

///////////////////////////////////////
// VIOB POK (Always ON)
///////////////////////////////////////
logic viob_pok;
logic viob_pok_int;

vio_pgd u_viob_pok (
  .vio_pok_o ( viob_pok_int )
);

assign viob_pok = viob_pok_int && viob_supp_i;
assign ast_pwst_o.io_pok[1] = vcaon_pok && viob_pok;
assign mux_iob_sel_o = 4'h0;

///////////////////////////////////////
// Regulators & PDM Logic (VCC)
///////////////////////////////////////
logic deep_sleep;
logic main_pd, por_sync;

assign main_pd = !main_pd_ni;
assign por_sync = !por_sync_n;

rglts_pdm_3p3v u_rglts_pdm_3p3v (
  .vcc_pok_h_i ( vcc_pok_h ),
  .vcaon_pok_por_h_i ( vcaon_pok_por_src ),
  .vcmain_pok_por_h_i ( vcmain_pok_por_src ),
  .vio_pok_h_i ( ast_pwst_o.io_pok[1:0] ),
  .clk_src_aon_h_i ( clk_aon ),
  .main_pd_h_i ( main_pd ),
  .por_sync_h_i ( por_sync ),
  .scan_mode_h_i ( scan_mode ),
  .otp_power_seq_h_i ( otp_power_seq_i[2-1:0] ),
  .vcaon_supp_i ( vcaon_supp_i ),
  .vcmain_supp_i ( vcmain_supp_i ),
  .rglssm_vmppr_h_o ( rglssm_vmppr ),
  .rglssm_vcmon_h_o ( rglssm_vcmon ),
  .rglssm_brout_h_o ( rglssm_brout ),
  .vcmain_pok_h_o ( vcmain_pok_h ),
  .vcmain_pok_por_h_o ( ast_pwst_h_o.main_pok ),
  .vcaon_pok_h_o ( vcaon_pok_h ),
  .vcaon_pok_1p1_h_o ( vcaon_pok ),
  .vcaon_pok_por_h_o ( ast_pwst_h_o.aon_pok ),
  .vio_pok_h_o ( ast_pwst_h_o.io_pok[2-1:0] ),
  .vcc_pok_str_h_o ( ast_pwst_h_o.vcc_pok ),
  .vcc_pok_str_1p1_h_o ( vcc_pok_str ),
  .deep_sleep_h_o ( deep_sleep ),
  .flash_power_down_h_o ( flash_power_down_h_o ),
  .flash_power_ready_h_o ( flash_power_ready_h_o ),
  .otp_power_seq_h_o ( otp_power_seq_h_o[2-1:0] )
);

assign ast_pwst_o.vcc_pok = vcc_pok_str;

///////////////////////////////////////
///////////////////////////////////////
// Clocks Oscillattors
///////////////////////////////////////
///////////////////////////////////////

// System Clock, USB Clock, IO Clock moved to ast_main.sv
// Keep reset signals for inter-domain communication
logic rst_sys_clk_n, rst_io_clk_n, rst_usb_clk_n;
assign rst_sys_clk_n = vcmain_pok_por && vcc_pok;
assign rst_io_clk_n  = vcmain_pok_por && vcc_pok;
assign rst_usb_clk_n = vcmain_pok_por && vcc_pok;

logic sys_io_osc_cal;
logic usb_osc_cal;

///////////////////////////////////////
// AON Clock (Always ON)
///////////////////////////////////////
logic rst_aon_clk_n;
logic clk_src_aon_en, clk_osc_aon, clk_osc_aon_val;
logic aon_osc_cal;

`ifdef AST_BYPASS_CLK
logic clk_aon_ext;
assign clk_aon_ext = clk_osc_byp_i.aon;
`endif

assign rst_aon_clk_n = vcc_pok_str && vcaon_pok;
assign clk_src_aon_en = 1'b1;  // Always Enabled

aon_clk  u_aon_clk (
  .vcore_pok_h_i ( vcaon_pok_h ),
  .clk_aon_pd_ni ( 1'b1 ),     // Always Enabled
  .rst_aon_clk_ni ( rst_aon_clk_n ),
  .clk_src_aon_en_i ( clk_src_aon_en ),
  .scan_mode_i ( scan_mode ),
  .aon_osc_cal_i ( aon_osc_cal ),
`ifdef AST_BYPASS_CLK
  .clk_aon_ext_i ( clk_aon_ext ),
`endif
  .clk_src_aon_o ( clk_osc_aon ),
  .clk_src_aon_val_o ( clk_osc_aon_val )
);

logic vcmpp_aon_sync_n, rst_vcmpp_aon_n;

// Reset De-Assert Sync
prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_rst_vcmpp_aon_dasrt (
  .clk_i ( clk_aon ),
  .rst_ni ( vcmain_pok_por ),
  .d_i ( 1'b1 ),
  .q_o ( vcmpp_aon_sync_n )
);

assign rst_vcmpp_aon_n = scan_mode ? scan_reset_n : vcmpp_aon_sync_n;
// IO Clock moved to ast_main.sv

///////////////////////////////////////
// AST Clocks Bypass
///////////////////////////////////////
// AON clock only in ast_aon, SYS/IO/USB handled by ast_main
logic clk_src_aon;

// Inter-domain interface signal for clock bypass (clks_byp_main_to_aon declared earlier)
ast_aon_main_pkg::clks_byp_aon_to_main_t clks_byp_aon_to_main;

// AON clock bypass - simplified for OS domain-split
ast_clks_byp_aon u_ast_clks_byp_aon (
  .vcaon_pok_i ( vcaon_pok ),
  .vcmain_pok_i ( vcmain_pok_h ),
  .scan_mode_i ( scan_mode ),
  .scan_reset_ni ( scan_reset_n ),
  .clk_osc_aon_i ( clk_osc_aon ),
  .clk_osc_aon_val_i ( clk_osc_aon_val ),
  .main_to_aon_i ( clks_byp_main_to_aon ),
  .aon_to_main_o ( clks_byp_aon_to_main )
);

assign clk_src_aon = clks_byp_aon_to_main.clk_src_aon_o;
assign clk_src_aon_val_o = clks_byp_aon_to_main.clk_src_aon_val_o;

// AON source clock buffer
////////////////////////////////////////
prim_clock_buf #(
  .NoFpgaBuf ( 1'b1 )
) u_clk_src_aon_buf (
  .clk_i ( clk_src_aon ),
  .clk_o ( clk_src_aon_o )
);

///////////////////////////////////////
// ADC (Always ON)
///////////////////////////////////////
adc #(
  .AdcCnvtClks ( AdcCnvtClks ),
  .AdcChannels ( ast_pkg::AdcChannels ),
  .AdcDataWidth ( ast_pkg::AdcDataWidth )
) u_adc (
  .adc_a0_ai ( adc_a0_ai ),
  .adc_a1_ai ( adc_a1_ai ),
  .adc_chnsel_i ( adc_chnsel_i[ast_pkg::AdcChannels-1:0] ),
  .adc_pd_i ( adc_pd_i ),
  .clk_adc_i ( clk_ast_adc_i ),
  .rst_adc_ni ( rst_ast_adc_ni ),
  .adc_d_o ( adc_d_o[ast_pkg::AdcDataWidth-1:0] ),
  .adc_d_val_o ( adc_d_val_o )
);

///////////////////////////////////////
// Alerts (Always ON)
///////////////////////////////////////
ast_pkg::ast_dif_t as_alert_src;
ast_pkg::ast_dif_t cgc_alert_src;
ast_pkg::ast_dif_t gd_alert_src;
ast_pkg::ast_dif_t ot0_alert_src;
ast_pkg::ast_dif_t ts_alert_hi_src;
ast_pkg::ast_dif_t ts_alert_lo_src;
ast_pkg::ast_dif_t ot1_alert_src;
ast_pkg::ast_dif_t ot2_alert_src;
ast_pkg::ast_dif_t ot3_alert_src;
ast_pkg::ast_dif_t ot4_alert_src;
ast_pkg::ast_dif_t ot5_alert_src;


// Active Shield (AS)
///////////////////////////////////////
ast_alert u_alert_as (
  .clk_i ( clk_ast_alert_i ),
  .rst_ni ( rst_ast_alert_ni ),
  .alert_src_i ( as_alert_src ),
  .alert_trig_i ( alert_rsp_i.alerts_trig[ast_pkg::AsSel] ),
  .alert_ack_i ( alert_rsp_i.alerts_ack[ast_pkg::AsSel] ),
  .alert_req_o ( alert_req_o.alerts[ast_pkg::AsSel] )
);

// Clock Glitch (CG)
///////////////////////////////////////
ast_alert u_alert_cg (
  .clk_i ( clk_ast_alert_i ),
  .rst_ni ( rst_ast_alert_ni ),
  .alert_src_i ( cgc_alert_src ),
  .alert_trig_i ( alert_rsp_i.alerts_trig[ast_pkg::CgSel] ),
  .alert_ack_i ( alert_rsp_i.alerts_ack[ast_pkg::CgSel] ),
  .alert_req_o ( alert_req_o.alerts[ast_pkg::CgSel] )
);

// Glitch Detector (GD)
///////////////////////////////////////
ast_alert u_alert_gd (
  .clk_i ( clk_ast_alert_i ),
  .rst_ni ( rst_ast_alert_ni ),
  .alert_src_i ( gd_alert_src ),
  .alert_trig_i ( alert_rsp_i.alerts_trig[ast_pkg::GdSel] ),
  .alert_ack_i ( alert_rsp_i.alerts_ack[ast_pkg::GdSel] ),
  .alert_req_o ( alert_req_o.alerts[ast_pkg::GdSel] )
);

// Temprature Sensor High (TS Hi)
///////////////////////////////////////
ast_alert u_alert_ts_hi (
  .clk_i ( clk_ast_alert_i ),
  .rst_ni ( rst_ast_alert_ni ),
  .alert_src_i ( ts_alert_hi_src ),
  .alert_trig_i ( alert_rsp_i.alerts_trig[ast_pkg::TsHiSel] ),
  .alert_ack_i ( alert_rsp_i.alerts_ack[ast_pkg::TsHiSel] ),
  .alert_req_o ( alert_req_o.alerts[ast_pkg::TsHiSel] )
);

// Temprature Sensor Low (TS Lo)
///////////////////////////////////////
ast_alert u_alert_ts_lo (
  .clk_i ( clk_ast_alert_i ),
  .rst_ni ( rst_ast_alert_ni ),
  .alert_src_i ( ts_alert_lo_src ),
  .alert_trig_i ( alert_rsp_i.alerts_trig[ast_pkg::TsLoSel] ),
  .alert_ack_i ( alert_rsp_i.alerts_ack[ast_pkg::TsLoSel] ),
  .alert_req_o ( alert_req_o.alerts[ast_pkg::TsLoSel] )
);

// Other-0 Alert (OT0)
///////////////////////////////////////
ast_alert u_alert_ot0 (
  .clk_i ( clk_ast_alert_i ),
  .rst_ni ( rst_ast_alert_ni ),
  .alert_src_i ( ot0_alert_src ),
  .alert_trig_i ( alert_rsp_i.alerts_trig[ast_pkg::Ot0Sel] ),
  .alert_ack_i ( alert_rsp_i.alerts_ack[ast_pkg::Ot0Sel] ),
  .alert_req_o ( alert_req_o.alerts[ast_pkg::Ot0Sel] )
); // of u_alert_ot0

// Other-1 Alert (OT1)
///////////////////////////////////////
ast_alert u_alert_ot1 (
  .clk_i ( clk_ast_alert_i ),
  .rst_ni ( rst_ast_alert_ni ),
  .alert_src_i ( ot1_alert_src ),
  .alert_trig_i ( alert_rsp_i.alerts_trig[ast_pkg::Ot1Sel] ),
  .alert_ack_i ( alert_rsp_i.alerts_ack[ast_pkg::Ot1Sel] ),
  .alert_req_o ( alert_req_o.alerts[ast_pkg::Ot1Sel] )
); // of u_alert_ot1

// Other-2 Alert (OT2)
///////////////////////////////////////
ast_alert u_alert_ot2 (
  .clk_i ( clk_ast_alert_i ),
  .rst_ni ( rst_ast_alert_ni ),
  .alert_src_i ( ot2_alert_src ),
  .alert_trig_i ( alert_rsp_i.alerts_trig[Ot2Sel] ),
  .alert_ack_i ( alert_rsp_i.alerts_ack[Ot2Sel] ),
  .alert_req_o ( alert_req_o.alerts[Ot2Sel] )
); // of u_alert_ot2

// Other-3 Alert (OT3)
///////////////////////////////////////
ast_alert u_alert_ot3 (
  .clk_i ( clk_ast_alert_i ),
  .rst_ni ( rst_ast_alert_ni ),
  .alert_src_i ( ot3_alert_src ),
  .alert_trig_i ( alert_rsp_i.alerts_trig[Ot3Sel] ),
  .alert_ack_i ( alert_rsp_i.alerts_ack[Ot3Sel] ),
  .alert_req_o ( alert_req_o.alerts[Ot3Sel] )
); // of u_alert_ot3

// Other-4 Alert (OT4)
///////////////////////////////////////
ast_alert u_alert_ot4 (
  .clk_i ( clk_ast_alert_i ),
  .rst_ni ( rst_ast_alert_ni ),
  .alert_src_i ( ot4_alert_src ),
  .alert_trig_i ( alert_rsp_i.alerts_trig[ast_pkg::Ot4Sel] ),
  .alert_ack_i ( alert_rsp_i.alerts_ack[ast_pkg::Ot4Sel] ),
  .alert_req_o ( alert_req_o.alerts[ast_pkg::Ot4Sel] )
); // of u_alert_ot4

// Other-5 Alert (OT5)
///////////////////////////////////////
ast_alert u_alert_ot5 (
  .clk_i ( clk_ast_alert_i ),
  .rst_ni ( rst_ast_alert_ni ),
  .alert_src_i ( ot5_alert_src ),
  .alert_trig_i ( alert_rsp_i.alerts_trig[ast_pkg::Ot5Sel] ),
  .alert_ack_i ( alert_rsp_i.alerts_ack[ast_pkg::Ot5Sel] ),
  .alert_req_o ( alert_req_o.alerts[ast_pkg::Ot5Sel] )
); // of u_alert_ot5

// Alerts Open-Source Selection
////////////////////////////////////////
assign as_alert_src    = '{p: 1'b0, n: 1'b1};
assign cgc_alert_src   = '{p: 1'b0, n: 1'b1};
assign gd_alert_src    = '{p: 1'b0, n: 1'b1};
assign ts_alert_hi_src = '{p: 1'b0, n: 1'b1};
assign ts_alert_lo_src = '{p: 1'b0, n: 1'b1};
assign ot1_alert_src   = '{p: 1'b0, n: 1'b1};
assign ot2_alert_src   = '{p: 1'b0, n: 1'b1};
assign ot3_alert_src   = '{p: 1'b0, n: 1'b1};
assign ot4_alert_src   = '{p: 1'b0, n: 1'b1};
assign ot5_alert_src   = '{p: 1'b0, n: 1'b1};

///////////////////////////////////////
// AST Registers (Always ON)
///////////////////////////////////////

// TLUL Integrity Error (from main domain)
assign ot0_alert_src = main_to_aon_i.ot0_alert_src;

// Calibration signals - simple initialization for OS
// (REGAL register and ast_init_done_o are now in ast_main.sv)
always_ff @( posedge clk_ast_tlul_i, negedge rst_ast_tlul_ni ) begin
  if ( !rst_ast_tlul_ni ) begin
    sys_io_osc_cal <= 1'b0;
  end else begin
    sys_io_osc_cal <= 1'b1;
  end
end

always_ff @( posedge clk_ast_tlul_i, negedge vcaon_pok_por ) begin
  if ( !vcaon_pok_por ) begin
    usb_osc_cal <= 1'b0;
  end else begin
    usb_osc_cal <= 1'b1;
  end
end

always_ff @( posedge clk_ast_tlul_i, negedge vcaon_pok ) begin
  if ( !vcaon_pok ) begin
    aon_osc_cal <= 1'b0;
  end else begin
    aon_osc_cal <= 1'b1;
  end
end

// USB PU-P and PU-N value selection
assign usb_io_pu_cal_o = ast_pkg::UsbCalibWidth'(1 << (ast_pkg::UsbCalibWidth[5-1:0]/2));

///////////////////////////////////////
// DFT (Main | Always ON)
///////////////////////////////////////
ast_dft u_ast_dft (
  .obs_ctrl_o ( obs_ctrl_o ),
  .ast2padmux_o ( ast2padmux_o[ast_pkg::Ast2PadOutWidth-1:0] ),
  .dpram_rmf_o ( dpram_rmf_o ),
  .dpram_rml_o ( dpram_rml_o ),
  .spram_rm_o ( spram_rm_o ),
  .sprgf_rm_o ( sprgf_rm_o ),
  .sprom_rm_o ( sprom_rm_o )
);

////////////////////////////////////////
// DFT Misc Logic
////////////////////////////////////////
`ifdef ANALOGSIM
assign ast2pad_t0_ao = 0.0;
assign ast2pad_t1_ao = 0.1;
`else
assign ast2pad_t0_ao = 1'bz;
assign ast2pad_t1_ao = 1'bz;
`endif

////////////////////////////////////////
// Inter-domain communication (OS simplified)
////////////////////////////////////////
// Power signals
assign aon_to_main_o.pwr.vcc_pok = vcc_pok;
assign aon_to_main_o.pwr.vcaon_pok = vcaon_pok;
assign aon_to_main_o.pwr.vcmain_pok_h = vcmain_pok_h;
assign aon_to_main_o.pwr.vcmain_pok_por = vcmain_pok_por;
assign aon_to_main_o.pwr.vcc_pok_str = vcc_pok_str;

// Clock and reset signals
assign aon_to_main_o.clk_rst.clk_aon = clk_aon;
assign aon_to_main_o.clk_rst.clk_ast_tlul = clk_ast_tlul_i;
assign aon_to_main_o.clk_rst.rst_ast_tlul_n = rst_ast_tlul_ni;
assign aon_to_main_o.clk_rst.clk_ast_rng = clk_ast_rng_i;
assign aon_to_main_o.clk_rst.rst_ast_rng_n = rst_ast_rng_ni;
assign aon_to_main_o.clk_rst.clk_ast_es = clk_ast_es_i;
assign aon_to_main_o.clk_rst.rst_ast_es_n = rst_ast_es_ni;
assign aon_to_main_o.clk_rst.rst_sys_clk_n = rst_sys_clk_n;
assign aon_to_main_o.clk_rst.rst_io_clk_n = rst_io_clk_n;
assign aon_to_main_o.clk_rst.rst_usb_clk_n = rst_usb_clk_n;

// Clock bypass interface (OS uses monolithic ast_clks_byp, provide defaults)
assign aon_to_main_o.clks_byp = clks_byp_aon_to_main;

// Oscillator control interface
assign aon_to_main_o.clk_osc.deep_sleep = deep_sleep;
assign aon_to_main_o.clk_osc.usb_ref_pulse = usb_ref_pulse_i;
assign aon_to_main_o.clk_osc.usb_ref_val = usb_ref_val_i;

// Scan signals
assign aon_to_main_o.scan_mode = scan_mode;
assign aon_to_main_o.scan_reset_n = scan_reset_n;

// Calibration signals
assign aon_to_main_o.sys_io_osc_cal = sys_io_osc_cal;
assign aon_to_main_o.usb_osc_cal = usb_osc_cal;

// Clock outputs and bypass acks now directly output from ast_main

////////////////
// Assertions //
////////////////

// Clocks
`ASSERT_KNOWN(ClkSrcAonKnownO_A, clk_src_aon_o, 1, ast_pwst_o.aon_pok)
`ASSERT_KNOWN(ClkSrcAonValKnownO_A, clk_src_aon_val_o, clk_src_aon_o, rst_aon_clk_n)
//
`ASSERT_KNOWN(UsbIoPuCalKnownO_A, usb_io_pu_cal_o, clk_ast_tlul_i, ast_pwst_o.aon_pok)
// ADC
`ASSERT_KNOWN(AdcDKnownO_A, adc_d_o, clk_ast_adc_i, rst_ast_adc_ni)
`ASSERT_KNOWN(AdcDValKnownO_A, adc_d_val_o, clk_ast_adc_i, rst_ast_adc_ni)
// Note: RNG assertions moved to ast_main.sv
// TLUL and InitDone asserts are now in ast_main.sv
// POs
`ASSERT_KNOWN(VcaonPokKnownO_A, ast_pwst_o.aon_pok, clk_src_aon_o, por_ni)
`ASSERT_KNOWN(VcmainPokKnownO_A, ast_pwst_o.main_pok, clk_src_aon_o, por_ni)
`ASSERT_KNOWN(VioaPokKnownO_A, ast_pwst_o.io_pok[0], clk_src_aon_o, por_ni)
`ASSERT_KNOWN(ViobPokKnownO_A, ast_pwst_o.io_pok[1], clk_src_aon_o, por_ni)
`ASSERT_KNOWN(VcaonPokHKnownO_A, ast_pwst_h_o.aon_pok, clk_src_aon_o, por_ni)
`ASSERT_KNOWN(VcmainPokHKnownO_A, ast_pwst_h_o.main_pok, clk_src_aon_o, por_ni)
`ASSERT_KNOWN(VioaPokHKnownO_A, ast_pwst_h_o.io_pok[0], clk_src_aon_o, por_ni)
`ASSERT_KNOWN(ViobPokHKnownO_A, ast_pwst_h_o.io_pok[1], clk_src_aon_o, por_ni)
// FLASH/OTP
`ASSERT_KNOWN(FlashPowerDownKnownO_A, flash_power_down_h_o, 1, ast_pwst_o.main_pok)
`ASSERT_KNOWN(FlashPowerReadyKnownO_A, flash_power_ready_h_o, 1, ast_pwst_o.main_pok)
`ASSERT_KNOWN(OtpPowerSeqKnownO_A, otp_power_seq_h_o, 1, ast_pwst_o.main_pok)
// Alerts
`ASSERT_KNOWN(AlertReqKnownO_A, alert_req_o, clk_ast_alert_i, rst_ast_alert_ni)
// DPRAM/SPRAM
`ASSERT_KNOWN(DpramRmfKnownO_A, dpram_rmf_o, clk_ast_tlul_i, ast_pwst_o.aon_pok)
`ASSERT_KNOWN(DpramRmlKnownO_A, dpram_rml_o, clk_ast_tlul_i, ast_pwst_o.aon_pok)
`ASSERT_KNOWN(SpramRmKnownO_A, spram_rm_o, clk_ast_tlul_i, ast_pwst_o.aon_pok)
`ASSERT_KNOWN(SprgfRmKnownO_A, sprgf_rm_o, clk_ast_tlul_i, ast_pwst_o.aon_pok)
`ASSERT_KNOWN(SpromRmKnownO_A, sprom_rm_o, clk_ast_tlul_i, ast_pwst_o.aon_pok)
// DFT
`ASSERT_KNOWN(Ast2PadmuxKnownO_A, ast2padmux_o, clk_ast_tlul_i, ast_pwst_o.aon_pok)
// SCAN
`ASSERT_KNOWN(DftScanMdKnownO_A, dft_scan_md_o, clk_ast_tlul_i, ast_pwst_o.aon_pok)
`ASSERT_KNOWN(ScanShiftEnKnownO_A, scan_shift_en_o, clk_ast_tlul_i, ast_pwst_o.aon_pok)
`ASSERT_KNOWN(ScanResetKnownO_A, scan_reset_no, clk_ast_tlul_i, ast_pwst_o.aon_pok)
`ASSERT_KNOWN(FlashBistEnKnownO_A, flash_bist_en_o, clk_ast_tlul_i, ast_pwst_o.aon_pok)

// Note: reg_we onehot assertion moved to ast_main.sv along with u_reg
/////////////////////
// Unused Signals  //
/////////////////////
logic unused_sigs;

assign unused_sigs = ^{ clk_ast_usb_i,
                        rst_ast_usb_ni,
                        sns_spi_ext_clk_i,
                        sns_clks_i,
                        sns_rsts_i,
                        shift_en,
                        main_env_iso_en_i,
                        rst_vcmpp_aon_n,
                        padmux2ast_i[ast_pkg::Pad2AstInWidth-1:0],
                        dft_strap_test_i.valid,
                        dft_strap_test_i.straps[1:0],
                        lc_dft_en_i[3:0],
                        fla_obs_i[8-1:0],
                        otp_obs_i[8-1:0],
                        otm_obs_i[8-1:0],
                        usb_obs_i,
                        clk_ast_ext_i,
                        clk_src_usb_en_i,
                        ext_freq_is_96m_i,
                        all_clk_byp_req_i,
                        io_clk_byp_req_i
                      };

endmodule : ast_aon
