// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// -------- W A R N I N G: A U T O - G E N E R A T E D  C O D E !! -------- //
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED.
//
//############################################################################
// *Name: ast
// *Module Description: Analog Sensors Top
//############################################################################

`include "prim_assert.sv"

module ast #(
  parameter int unsigned AdcChannels     = 2,
  parameter int unsigned AdcDataWidth    = 10,
  parameter int unsigned EntropyStreams  = 4,
  parameter int unsigned UsbCalibWidth   = 20,
  parameter int unsigned Ast2PadOutWidth = 9,
  parameter int unsigned Pad2AstInWidth  = 9
) (
  // tlul if
  input tlul_pkg::tl_h2d_t tl_i,              // TLUL H2D
  output tlul_pkg::tl_d2h_t tl_o,             // TLUL D2H
  output prim_mubi_pkg::mubi4_t ast_init_done_o,  // AST (registers) Init Done

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

  // system source clock
  input clk_src_sys_en_i,                     // SYS Source Clock Enable
  input prim_mubi_pkg::mubi4_t clk_src_sys_jen_i,  // SYS Source Clock Jitter Enable
  output logic clk_src_sys_o,                 // SYS Source Clock
  output logic clk_src_sys_val_o,             // SYS Source Clock Valid

  // aon source clock
  output logic clk_src_aon_o,                 // AON Source Clock
  output logic clk_src_aon_val_o,             // AON Source Clock Valid

  // io source clock
  input clk_src_io_en_i,                      // IO Source Clock Enable
  output logic clk_src_io_o,                  // IO Source Clock
  output logic clk_src_io_val_o,              // IO Source Clock Valid
  output prim_mubi_pkg::mubi4_t clk_src_io_48m_o,  // IO Source Clock is 48MHz

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
  input rng_fips_i,                           // RNG FIPS
  output logic rng_val_o,                     // RNG Valid
  output logic [EntropyStreams-1:0] rng_b_o,  // RNG Bit(s)

  // entropy distribution interface
  input edn_pkg::edn_rsp_t entropy_rsp_i,     // Entropy Response
  output edn_pkg::edn_req_t entropy_req_o,    // Entropy Request

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
  input [Pad2AstInWidth-1:0] padmux2ast_i,    // IO_2_DFT Input Signals
  output logic [Ast2PadOutWidth-1:0] ast2padmux_o,  // DFT_2_IO Output Signals

`ifdef ANALOGSIM
  output real ast2pad_t0_ao,                  // AST_2_PAD Analog T0 Output Signal
  output real ast2pad_t1_ao,                  // AST_2_PAD Analog T1 Output Signal
`else
  output wire ast2pad_t0_ao,                  // AST_2_PAD Analog T0 Output Signal
  output wire ast2pad_t1_ao,                  // AST_2_PAD Analog T1 Output Signal
`endif

  // flash and external clocks
  input prim_mubi_pkg::mubi4_t ext_freq_is_96m_i,   // External clock frequecy is 96MHz
  input prim_mubi_pkg::mubi4_t all_clk_byp_req_i,   // All clocks bypass request
  output prim_mubi_pkg::mubi4_t all_clk_byp_ack_o,  // Switch all clocks to External clocks
  input prim_mubi_pkg::mubi4_t io_clk_byp_req_i,    // IO clock bypass request (for OTP bootstrap)
  output prim_mubi_pkg::mubi4_t io_clk_byp_ack_o,   // Switch IO clock to External clockn
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
  output scan_reset_no                          // Scan Reset output
);

import ast_pkg::* ;
import ast_reg_pkg::* ;
import ast_bhv_pkg::* ;

logic scan_mode, shift_en, scan_reset_n;
logic vcc_pok, vcc_pok_h, vcc_pok_str;
logic vcaon_pok, vcaon_pok_h, vcmain_pok;
logic vcaon_pok_por, vcmain_pok_por;

// Local (AST) System clock buffer
////////////////////////////////////////
logic clk_sys;

prim_clock_buf #(
  .NoFpgaBuf ( 1'b1 )
) u_clk_sys_buf (
  .clk_i ( clk_src_sys_o ),
  .clk_o ( clk_sys )
);

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
//
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
assign vcaon_pok_por_lat = rglssm_brout || vcaon_pok_por_src;
assign ast_pwst_o.aon_pok = vcaon_pok_por_lat;
assign vcaon_pok_por = scan_mode ? scan_reset_n : vcaon_pok_por_lat;


////////////////////////////////////////
// VCMAIN POK POR (Always ON)
///////////////////////////////////////
logic rglssm_vmppr, vcmain_pok_por_src;

assign vcmain_pok_por_src = vcaon_pok_por_lat && vcmain_pok && !rglssm_vmppr;
assign ast_pwst_o.main_pok = vcmain_pok_por_src;
assign vcmain_pok_por = scan_mode ? scan_reset_n : vcmain_pok_por_src;


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
  .vcmain_pok_h_o ( vcmain_pok ),
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


///////////////////////////////////////
// System Clock (Always ON)
///////////////////////////////////////
logic rst_sys_clk_n, clk_sys_pd_n;
logic clk_sys_en, clk_osc_sys, clk_osc_sys_val;
prim_mubi_pkg::mubi4_t clk_src_sys_jen;

assign rst_sys_clk_n = vcmain_pok_por && vcc_pok;
assign clk_sys_pd_n  = scan_mode || !deep_sleep;

logic sys_io_osc_cal;

assign clk_sys_en = clk_src_sys_en_i;

`ifdef AST_BYPASS_CLK
logic clk_sys_ext;
assign clk_sys_ext = clk_osc_byp_i.sys;
`endif

sys_clk u_sys_clk (
  .clk_src_sys_jen_i ( prim_mubi_pkg::mubi4_test_true_loose(clk_src_sys_jen) ),
  .clk_src_sys_en_i ( clk_sys_en ),
  .clk_sys_pd_ni ( clk_sys_pd_n ),
  .rst_sys_clk_ni ( rst_sys_clk_n ),
  .vcore_pok_h_i ( vcaon_pok_h ),
  .scan_mode_i ( scan_mode ),
  .sys_osc_cal_i ( sys_io_osc_cal ),
`ifdef AST_BYPASS_CLK
  .clk_sys_ext_i ( clk_sys_ext ),
`endif
  .clk_src_sys_o ( clk_osc_sys ),
  .clk_src_sys_val_o ( clk_osc_sys_val )
);


///////////////////////////////////////
// USB Clock (Always ON)
///////////////////////////////////////
logic rst_usb_clk_n, clk_usb_pd_n;
logic clk_usb_en, clk_osc_usb, clk_osc_usb_val;
logic usb_ref_val, usb_ref_pulse;

assign rst_usb_clk_n = vcmain_pok_por && vcc_pok;
assign clk_usb_pd_n  = scan_mode || !deep_sleep;

logic usb_osc_cal;

`ifdef AST_BYPASS_CLK
logic clk_usb_ext;
assign clk_usb_ext = clk_osc_byp_i.usb;
`endif

assign clk_usb_en = clk_src_usb_en_i;
assign usb_ref_val = usb_ref_val_i;
assign usb_ref_pulse = usb_ref_pulse_i;

usb_clk u_usb_clk (
  .vcore_pok_h_i ( vcaon_pok_h ),
  .clk_usb_pd_ni ( clk_usb_pd_n ),
  .rst_usb_clk_ni ( rst_usb_clk_n ),
  .clk_src_usb_en_i ( clk_usb_en ),
  .usb_ref_val_i ( usb_ref_val ),
  .usb_ref_pulse_i ( usb_ref_pulse ),
  .clk_ast_usb_i ( clk_ast_usb_i ),
  .rst_ast_usb_ni ( rst_ast_usb_ni ),
  .scan_mode_i ( scan_mode ),
  .usb_osc_cal_i ( usb_osc_cal ),
`ifdef AST_BYPASS_CLK
  .clk_usb_ext_i ( clk_usb_ext ),
`endif
  .clk_src_usb_o ( clk_osc_usb ),
  .clk_src_usb_val_o ( clk_osc_usb_val )
);


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


///////////////////////////////////////
// IO Clock (Always ON)
///////////////////////////////////////
logic rst_io_clk_n, clk_io_pd_n;
logic clk_src_io_en, clk_osc_io, clk_osc_io_val;

assign rst_io_clk_n = vcmain_pok_por && vcc_pok;
assign clk_io_pd_n  = scan_mode || !deep_sleep;

`ifdef AST_BYPASS_CLK
logic clk_io_ext;
assign clk_io_ext = clk_osc_byp_i.io;
`endif

assign clk_src_io_en = clk_src_io_en_i;

io_clk u_io_clk (
  .vcore_pok_h_i ( vcaon_pok_h ),
  .clk_io_pd_ni ( clk_io_pd_n ),
  .rst_io_clk_ni ( rst_io_clk_n ),
  .clk_src_io_en_i ( clk_src_io_en ),
  .scan_mode_i ( scan_mode ),
  .io_osc_cal_i ( sys_io_osc_cal ),
`ifdef AST_BYPASS_CLK
  .clk_io_ext_i ( clk_io_ext ),
`endif
  .clk_src_io_o ( clk_osc_io ),
  .clk_src_io_val_o ( clk_osc_io_val )
);


///////////////////////////////////////
// AST Clocks Bypass
///////////////////////////////////////
logic clk_src_sys, clk_src_io, clk_src_usb, clk_src_aon;

ast_clks_byp u_ast_clks_byp (
  .vcaon_pok_i ( vcaon_pok ),
  .deep_sleep_i ( deep_sleep ),
  .clk_src_sys_en_i ( clk_src_sys_en_i ),
  .clk_osc_sys_i ( clk_osc_sys ),
  .clk_osc_sys_val_i ( clk_osc_sys_val ),
  .clk_src_io_en_i ( clk_src_io_en_i ),
  .clk_osc_io_i ( clk_osc_io ),
  .clk_osc_io_val_i ( clk_osc_io_val ),
  .clk_src_usb_en_i ( clk_src_usb_en_i ),
  .clk_osc_usb_i ( clk_osc_usb ),
  .clk_osc_usb_val_i ( clk_osc_usb_val ),
  .clk_osc_aon_i ( clk_osc_aon ),
  .clk_osc_aon_val_i ( clk_osc_aon_val ),
  .clk_ast_ext_i ( clk_ast_ext_i ),
  .io_clk_byp_req_i ( io_clk_byp_req_i ),
  .all_clk_byp_req_i ( all_clk_byp_req_i ),
  .ext_freq_is_96m_i ( ext_freq_is_96m_i ),
  .io_clk_byp_ack_o ( io_clk_byp_ack_o ),
  .all_clk_byp_ack_o ( all_clk_byp_ack_o ),
  .clk_src_sys_o ( clk_src_sys ),
  .clk_src_sys_val_o ( clk_src_sys_val_o ),
  .clk_src_io_o ( clk_src_io ),
  .clk_src_io_val_o ( clk_src_io_val_o ),
  .clk_src_io_48m_o ( clk_src_io_48m_o ),
  .clk_src_usb_o ( clk_src_usb ),
  .clk_src_usb_val_o ( clk_src_usb_val_o ),
  .clk_src_aon_o ( clk_src_aon ),
  .clk_src_aon_val_o ( clk_src_aon_val_o )
);

// System source clock buffer
////////////////////////////////////////
prim_clock_buf #(
  .NoFpgaBuf ( 1'b1 )
) u_clk_src_sys_buf (
  .clk_i ( clk_src_sys ),
  .clk_o ( clk_src_sys_o )
);

// IO source clock buffer
////////////////////////////////////////
prim_clock_buf #(
  .NoFpgaBuf ( 1'b1 )
) u_clk_src_io_buf (
  .clk_i ( clk_src_io ),
  .clk_o ( clk_src_io_o )
);

// USB source clock buffer
////////////////////////////////////////
prim_clock_buf #(
  .NoFpgaBuf ( 1'b1 )
) u_clk_src_usb_buf (
  .clk_i ( clk_src_usb ),
  .clk_o ( clk_src_usb_o )
);

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
);


///////////////////////////////////////
// Entropy (Always ON)
///////////////////////////////////////
localparam int EntropyRateWidth = 4;
logic [EntropyRateWidth-1:0] entropy_rate;
logic vcmain_pok_por_sys, rst_src_sys_n;

// Sync clk_src_sys_jen_i to clk_sys
prim_mubi4_sync #(
  .NumCopies ( 1 ),
  .AsyncOn ( 1 ),
  .StabilityCheck ( 1 ),
  .ResetValue (prim_mubi_pkg::MuBi4False )
) u_jitter_en_sync (
  .clk_i ( clk_sys ),
  .rst_ni ( rst_src_sys_n ),
  .mubi_i ( clk_src_sys_jen_i ),
  .mubi_o ( {clk_src_sys_jen} )
);

// Reset De-Assert Sync
prim_flop_2sync #(
  .Width ( 1 ),
  .ResetValue ( 1'b0 )
) u_rst_sys_dasrt (
  .clk_i ( clk_sys ),
  .rst_ni ( vcmain_pok_por ),
  .d_i ( 1'b1 ),
  .q_o ( vcmain_pok_por_sys )
);

assign rst_src_sys_n = scan_mode ? scan_reset_n : vcmain_pok_por_sys;

`ifndef SYNTHESIS
logic [EntropyRateWidth-1:0] dv_entropy_rate_value;

initial begin : erate_plusargs
  dv_entropy_rate_value = EntropyRateWidth'($urandom_range(0, (2**EntropyRateWidth -1)));
  void'($value$plusargs("entropy_rate_value=%0d", dv_entropy_rate_value));
  `ASSERT_I(DvErateValueCheck, dv_entropy_rate_value inside {[0:(2**EntropyRateWidth -1)]})
end

assign entropy_rate = dv_entropy_rate_value;
`else
assign entropy_rate = EntropyRateWidth'(5);
`endif

ast_entropy #(
  .EntropyRateWidth ( EntropyRateWidth )
) u_entropy (
  .entropy_rsp_i ( entropy_rsp_i ),
  .entropy_rate_i ( entropy_rate[EntropyRateWidth-1:0] ),
  .clk_ast_es_i ( clk_ast_es_i ),
  .rst_ast_es_ni ( rst_ast_es_ni ),
  .clk_src_sys_i ( clk_sys ),
  .rst_src_sys_ni ( rst_src_sys_n ),
  .clk_src_sys_val_i ( clk_src_sys_val_o ),
  .clk_src_sys_jen_i ( prim_mubi_pkg::mubi4_test_true_loose(clk_src_sys_jen) ),
  .entropy_req_o ( entropy_req_o )
);


///////////////////////////////////////
// RNG (Always ON)
///////////////////////////////////////
ast_pkg::ast_dif_t ot1_alert_src;

rng #(
  .EntropyStreams ( EntropyStreams )
) u_rng (
  .clk_i ( clk_ast_tlul_i ),
  .rst_ni ( rst_ast_tlul_ni ),
  .clk_ast_rng_i ( clk_ast_rng_i ),
  .rst_ast_rng_ni ( rst_ast_rng_ni ),
  .rng_en_i ( rng_en_i ),
  .rng_fips_i ( rng_fips_i ),
  .scan_mode_i ( scan_mode ),
  .rng_b_o ( rng_b_o[EntropyStreams-1:0] ),
  .rng_val_o ( rng_val_o )
);


///////////////////////////////////////
// Alerts (Always ON)
///////////////////////////////////////
ast_pkg::ast_dif_t as_alert_src;
ast_pkg::ast_dif_t cg_alert_src;
ast_pkg::ast_dif_t gd_alert_src;
ast_pkg::ast_dif_t ts_alert_hi_src;
ast_pkg::ast_dif_t ts_alert_lo_src;
ast_pkg::ast_dif_t ot0_alert_src;
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
  .alert_src_i ( cg_alert_src ),
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
assign cg_alert_src    = '{p: 1'b0, n: 1'b1};
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
ast_reg_pkg::ast_reg2hw_t reg2hw; // Write (To HW)
ast_reg_pkg::ast_hw2reg_t hw2reg; // Read  (From HW)
logic intg_err;

ast_reg_top u_reg (
  .clk_i ( clk_ast_tlul_i ),
  .rst_ni ( rst_ast_tlul_ni ),
  .tl_i ( tl_i ),
  .tl_o ( tl_o ),
  .reg2hw ( reg2hw ),
  .hw2reg ( hw2reg ),
  .intg_err_o ( intg_err ),
  .devmode_i ( 1'b1 )
);


///////////////////////////////////////
// REGAL Register
///////////////////////////////////////
logic regal_rst_n;
assign regal_rst_n = rst_ast_tlul_ni;

logic regal_we;
logic [32-1:0] regal, regal_di;

assign regal_we = reg2hw.regal.qe;
assign regal_di = reg2hw.regal.q;
assign hw2reg.regal.d = regal;

// REGAL & AST init done indication
always_ff @( posedge clk_ast_tlul_i, negedge regal_rst_n ) begin
  if ( !regal_rst_n ) begin
    regal           <= ast_reg_pkg::AST_REGAL_RESVAL;
    ast_init_done_o <= prim_mubi_pkg::MuBi4False;
  end else if ( regal_we ) begin
    regal           <= regal_di;
    ast_init_done_o <= prim_mubi_pkg::MuBi4True;
  end
end

always_ff @( posedge clk_ast_tlul_i, negedge rst_ast_tlul_ni ) begin
  if ( !rst_ast_tlul_ni ) begin
    sys_io_osc_cal <= 1'b0;
  end else if ( regal_we ) begin
    sys_io_osc_cal <= 1'b1;
  end
end

always_ff @( posedge clk_ast_tlul_i, negedge vcaon_pok_por ) begin
  if ( !vcaon_pok_por ) begin
    usb_osc_cal <= 1'b0;
  end else if ( regal_we ) begin
    usb_osc_cal <= 1'b1;
  end
end

always_ff @( posedge clk_ast_tlul_i, negedge vcaon_pok ) begin
  if ( !vcaon_pok ) begin
    aon_osc_cal <= 1'b0;
  end else if ( regal_we ) begin
    aon_osc_cal <= 1'b1;
  end
end

// TLUL Integrity Error
assign ot0_alert_src = '{p: intg_err, n: !intg_err};

// USB PU-P and PU-N value selection
assign usb_io_pu_cal_o = UsbCalibWidth'(1 << (UsbCalibWidth[5-1:0]/2));


///////////////////////////////////////
// DFT (Main | Always ON)
///////////////////////////////////////
ast_dft u_ast_dft (
  .obs_ctrl_o ( obs_ctrl_o ),
  .ast2padmux_o ( ast2padmux_o[Ast2PadOutWidth-1:0] ),
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


////////////////
// Assertions //
////////////////

// Clocks
`ASSERT_KNOWN(ClkSrcAonKnownO_A, clk_src_aon_o, 1, ast_pwst_o.aon_pok)
`ASSERT_KNOWN(ClkSrcAonValKnownO_A, clk_src_aon_val_o, clk_src_aon_o, rst_aon_clk_n)
`ASSERT_KNOWN(ClkSrcIoKnownO_A, clk_src_io_o, 1, ast_pwst_o.main_pok)
`ASSERT_KNOWN(ClkSrcIoValKnownO_A, clk_src_io_val_o, clk_src_io_o, rst_io_clk_n)
`ASSERT_KNOWN(ClkSrcIo48mKnownO_A, clk_src_io_48m_o, clk_src_io_o, rst_io_clk_n)
`ASSERT_KNOWN(ClkSrcSysKnownO_A, clk_src_sys_o, 1, ast_pwst_o.main_pok)
`ASSERT_KNOWN(ClkSrcSysValKnownO_A, clk_src_sys_val_o, clk_src_sys_o, rst_sys_clk_n)
`ASSERT_KNOWN(ClkSrcUsbKnownO_A, clk_src_usb_o, 1, ast_pwst_o.main_pok)
`ASSERT_KNOWN(ClkSrcUsbValKnownO_A, clk_src_usb_val_o, clk_src_usb_o, rst_usb_clk_n)
//
`ASSERT_KNOWN(UsbIoPuCalKnownO_A, usb_io_pu_cal_o, clk_ast_tlul_i, ast_pwst_o.aon_pok)
`ASSERT_KNOWN(LcClkBypAckEnKnownO_A, io_clk_byp_ack_o, clk_ast_tlul_i, rst_ast_tlul_ni)
`ASSERT_KNOWN(AllClkBypAckEnKnownO_A, all_clk_byp_ack_o, clk_ast_tlul_i, rst_ast_tlul_ni)
// ADC
`ASSERT_KNOWN(AdcDKnownO_A, adc_d_o, clk_ast_adc_i, rst_ast_adc_ni)
`ASSERT_KNOWN(AdcDValKnownO_A, adc_d_val_o, clk_ast_adc_i, rst_ast_adc_ni)
// RNG
`ASSERT_KNOWN(RngBKnownO_A, rng_b_o, clk_ast_rng_i, rst_ast_rng_ni)
`ASSERT_KNOWN(RngValKnownO_A, rng_val_o, clk_ast_rng_i, rst_ast_rng_ni)
// TLUL
`ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid, clk_ast_tlul_i, rst_ast_tlul_ni)
`ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready, clk_ast_tlul_i, rst_ast_tlul_ni)
//
`ASSERT_KNOWN(InitDoneKnownO_A, ast_init_done_o, clk_ast_tlul_i, rst_ast_tlul_ni)
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
//
// ES
`ASSERT_KNOWN(EntropyReeqKnownO_A, entropy_req_o, clk_ast_es_i,rst_ast_es_ni)
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

// Alert assertions for reg_we onehot check
`ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ERR(RegWeOnehot_A,
   u_reg, alert_req_o.alerts[ast_pkg::Ot0Sel].p, , , clk_ast_alert_i, rst_ast_alert_ni)


/////////////////////
// Unused Signals  //
/////////////////////
logic unused_sigs;

assign unused_sigs = ^{ clk_ast_usb_i,
                        rst_ast_usb_ni,
                        sns_spi_ext_clk_i,
                        sns_clks_i,
                        sns_rsts_i,
                        intg_err,
                        shift_en,
                        main_env_iso_en_i,
                        rst_vcmpp_aon_n,
                        padmux2ast_i[Pad2AstInWidth-1:0],
                        dft_strap_test_i.valid,
                        dft_strap_test_i.straps[1:0],
                        lc_dft_en_i[3:0],
                        fla_obs_i[8-1:0],
                        otp_obs_i[8-1:0],
                        otm_obs_i[8-1:0],
                        usb_obs_i,
                        reg2hw.rega0,
                        reg2hw.rega1,
                        reg2hw.rega2,
                        reg2hw.rega3,
                        reg2hw.rega4,
                        reg2hw.rega5,
                        reg2hw.rega6,
                        reg2hw.rega7,
                        reg2hw.rega8,
                        reg2hw.rega9,
                        reg2hw.rega10,
                        reg2hw.rega11,
                        reg2hw.rega12,
                        reg2hw.rega13,
                        reg2hw.rega14,
                        reg2hw.rega15,
                        reg2hw.rega16,
                        reg2hw.rega17,
                        reg2hw.rega18,
                        reg2hw.rega19,
                        reg2hw.rega20,
                        reg2hw.rega21,
                        reg2hw.rega22,
                        reg2hw.rega23,
                        reg2hw.rega24,
                        reg2hw.rega25,
                        reg2hw.rega26,
                        reg2hw.rega27,
                        reg2hw.rega28,
                        reg2hw.rega29,
                        reg2hw.rega30,
                        reg2hw.rega31,
                        reg2hw.rega32,
                        reg2hw.rega33,
                        reg2hw.rega34,
                        reg2hw.rega35,
                        reg2hw.rega36,
                        reg2hw.rega37,
                        reg2hw.regb   // [0:3]
                      };

endmodule : ast
