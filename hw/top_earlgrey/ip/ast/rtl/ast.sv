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

module ast (
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
  output logic [ast_pkg::UsbCalibWidth-1:0] usb_io_pu_cal_o,  // USB IO Pull-up Calibration Setting

  // adc interface
  input adc_pd_i,                             // ADC Power Down
  input ast_pkg::awire_t adc_a0_ai,           // ADC A0 Analog Input
  input ast_pkg::awire_t adc_a1_ai,           // ADC A1 Analog Input
  input [ast_pkg::AdcChannels-1:0] adc_chnsel_i,       // ADC Channel Select
  output [ast_pkg::AdcDataWidth-1:0] adc_d_o,          // ADC Digital (per channel)
  output adc_d_val_o,                         // ADC Digital Valid

  // rng (entropy source) interface
  input rng_en_i,                             // RNG Enable
  input rng_fips_i,                           // RNG FIPS
  output logic rng_val_o,                     // RNG Valid
  output logic [ast_pkg::EntropyStreams-1:0] rng_b_o,  // RNG Bit(s)

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
  input [ast_pkg::Pad2AstInWidth-1:0] padmux2ast_i,    // IO_2_DFT Input Signals
  output logic [ast_pkg::Ast2PadOutWidth-1:0] ast2padmux_o,  // DFT_2_IO Output Signals
  output logic [4-1:0] mux_iob_sel_o, // iob or spi selector

  // analog test outputs
  output ast_pkg::awire_t ast2pad_t0_ao,                  // AST_2_PAD Analog T0 Output Signal
  output ast_pkg::awire_t ast2pad_t1_ao,                  // AST_2_PAD Analog T1 Output Signal

  // flash and external clocks
  input prim_mubi_pkg::mubi4_t ext_freq_is_96m_i,   // External clock frequency is 96MHz
  input prim_mubi_pkg::mubi4_t all_clk_byp_req_i,   // All clocks bypass request
  output prim_mubi_pkg::mubi4_t all_clk_byp_ack_o,  // Switch all clocks to External clocks
  input prim_mubi_pkg::mubi4_t io_clk_byp_req_i,    // IO clock bypass request (for OTP bootstrap)
  output prim_mubi_pkg::mubi4_t io_clk_byp_ack_o,   // Switch IO clock to External clockn
  output prim_mubi_pkg::mubi4_t flash_bist_en_o,    // Flush BIST (TAP) Enable

  // Memory configuration request/response interfaces
  output ast_pkg::ast_mem_cfg_req_t mem_cfg_req_o,
  input  ast_pkg::ast_mem_cfg_rsp_t mem_cfg_rsp_i,

  // Scan interface
  output prim_mubi_pkg::mubi4_t dft_scan_md_o,  // Scan Mode output
  output scan_shift_en_o,                       // Scan Shift Enable output
  output scan_reset_no                          // Scan Reset output
);

localparam int unsigned EntropyStreams  = ast_pkg::EntropyStreams;
localparam int unsigned UsbCalibWidth   = ast_pkg::UsbCalibWidth;
localparam int unsigned Pad2AstInWidth  = ast_pkg::Pad2AstInWidth;
localparam int unsigned Ast2PadOutWidth = ast_pkg::Ast2PadOutWidth;

// Intra-IP communication signals
ast_intraip_pkg::s2p_t intraip_s2p;
ast_intraip_pkg::p2s_t intraip_p2s;

// Clock bypass for OS FPGA
ast_pkg::clks_osc_byp_t clk_osc_byp;
`ifdef AST_BYPASS_CLK
  assign clk_osc_byp = clk_osc_byp_i;
`else
  assign clk_osc_byp = '0;
`endif

// Convert ADC signals to/from req/rsp
ast_pkg::adc_ast_req_t adc_req;
assign adc_req = '{
  pd:          adc_pd_i,
  channel_sel: adc_chnsel_i
};

ast_pkg::adc_ast_rsp_t adc_rsp;
assign adc_d_o = adc_rsp.data;
assign adc_d_val_o = adc_rsp.data_valid;

ast_pkg::ast_vx_supp_t vx_supp;
assign vx_supp = '{
  vcc:    vcc_supp_i,
  vcaon:  vcaon_supp_i,
  vcmain: vcmain_supp_i,
  vioa:   vioa_supp_i,
  viob:   viob_supp_i
};

ast_pkg::ast_obs_bus_t obs;
assign obs = '{
  fla_obs: fla_obs_i,
  otp_obs: otp_obs_i,
  otm_obs: otm_obs_i,
  usb_obs: usb_obs_i
};

ast_pkg::ast_mem_cfg_primary_req_t mem_cfg_primary_req;
ast_pkg::ast_mem_cfg_primary_rsp_t mem_cfg_primary_rsp;
ast_pkg::ast_mem_cfg_secondary_req_t mem_cfg_secondary_req;
ast_pkg::ast_mem_cfg_secondary_rsp_t mem_cfg_secondary_rsp;

assign mem_cfg_req_o = '{
  otbn_imem:                mem_cfg_primary_req.otbn_imem,
  otbn_dmem:                mem_cfg_primary_req.otbn_dmem,
  i2c0:                     mem_cfg_primary_req.i2c0,
  i2c1:                     mem_cfg_primary_req.i2c1,
  i2c2:                     mem_cfg_primary_req.i2c2,
  usbdev_ram:               mem_cfg_primary_req.usbdev_ram,
  rv_core_ibex_icache_tag:  mem_cfg_primary_req.rv_core_ibex_icache_tag,
  rv_core_ibex_icache_data: mem_cfg_primary_req.rv_core_ibex_icache_data,
  sram_ctrl_main:           mem_cfg_primary_req.sram_ctrl_main,
  sram_ctrl_sec:            mem_cfg_primary_req.sram_ctrl_sec,
  sram_ctrl_ret:            mem_cfg_secondary_req.sram_ctrl_ret,
  sram_ctrl_meta:           mem_cfg_primary_req.sram_ctrl_meta,
  spi_device_sys2spi:       mem_cfg_primary_req.spi_device_sys2spi,
  spi_device_spi2sys:       mem_cfg_primary_req.spi_device_spi2sys,
  rom_ctrl_rom:             mem_cfg_primary_req.rom_ctrl_rom
};

assign mem_cfg_primary_rsp = '{
  otbn_imem: mem_cfg_rsp_i.otbn_imem,
  otbn_dmem: mem_cfg_rsp_i.otbn_dmem,
  i2c0: mem_cfg_rsp_i.i2c0,
  i2c1: mem_cfg_rsp_i.i2c1,
  i2c2: mem_cfg_rsp_i.i2c2,
  usbdev_ram: mem_cfg_rsp_i.usbdev_ram,
  rv_core_ibex_icache_tag: mem_cfg_rsp_i.rv_core_ibex_icache_tag,
  rv_core_ibex_icache_data: mem_cfg_rsp_i.rv_core_ibex_icache_data,
  sram_ctrl_main: mem_cfg_rsp_i.sram_ctrl_main,
  sram_ctrl_sec: mem_cfg_rsp_i.sram_ctrl_sec,
  sram_ctrl_meta: mem_cfg_rsp_i.sram_ctrl_meta,
  spi_device_sys2spi: mem_cfg_rsp_i.spi_device_sys2spi,
  spi_device_spi2sys: mem_cfg_rsp_i.spi_device_spi2sys,
  rom_ctrl_rom: mem_cfg_rsp_i.rom_ctrl_rom
};

assign mem_cfg_secondary_rsp = '{
  sram_ctrl_ret: mem_cfg_rsp_i.sram_ctrl_ret
};

// AON Domain instantiation
ast_part_secondary #(
  .UsbCalibWidth   ( UsbCalibWidth ),
  .Pad2AstInWidth  ( Pad2AstInWidth ),
  .Ast2PadOutWidth ( Ast2PadOutWidth )
) u_ast_part_secondary (
  .clk_ast_adc_i           ( clk_ast_adc_i ),
  .rst_ast_adc_ni          ( rst_ast_adc_ni ),
  .clk_ast_alert_i         ( clk_ast_alert_i ),
  .rst_ast_alert_ni        ( rst_ast_alert_ni ),
  .clk_ast_es_i            ( clk_ast_es_i ),
  .rst_ast_es_ni           ( rst_ast_es_ni ),
  .clk_ast_rng_i           ( clk_ast_rng_i ),
  .rst_ast_rng_ni          ( rst_ast_rng_ni ),
  .clk_ast_tlul_i          ( clk_ast_tlul_i ),
  .rst_ast_tlul_ni         ( rst_ast_tlul_ni ),
  .clk_ast_ext_i           ( clk_ast_ext_i ),
  .por_n_i                 ( por_ni ),
  .sns_clks_i              ( sns_clks_i ),
  .sns_rsts_i              ( sns_rsts_i ),
  .sns_spi_ext_clk_i       ( sns_spi_ext_clk_i ),
  .vx_supp_i               ( vx_supp ),
  .ast_pwst_o              ( ast_pwst_o ),
  .ast_pwst_h_o            ( ast_pwst_h_o ),
  .rstmgr_por_n_o          ( ), // Unused - part of ast_pwst
  .main_pd_n_i             ( main_pd_ni ),
  .main_env_iso_en_i       ( main_env_iso_en_i ),
  .flash_power_down_h_o    ( flash_power_down_h_o ),
  .flash_power_ready_h_o   ( flash_power_ready_h_o ),
  .otp_power_seq_i         ( otp_power_seq_i ),
  .otp_power_seq_h_o       ( otp_power_seq_h_o ),
  .clk_src_aon_o           ( clk_src_aon_o ),
  .clk_src_aon_val_o       ( clk_src_aon_val_o ),
  .usb_ref_pulse_i         ( usb_ref_pulse_i ),
  .usb_ref_val_i           ( usb_ref_val_i ),
  .clk_ast_usb_i           ( clk_ast_usb_i ),
  .rst_ast_usb_ni          ( rst_ast_usb_ni ),
  .clk_src_usb_en_i        ( clk_src_usb_en_i ),
  .usb_io_pu_cal_o         ( usb_io_pu_cal_o ),
  .adc_i                   ( adc_req ),
  .adc_o                   ( adc_rsp ),
  .adc_a0_a_i              ( adc_a0_ai ),
  .adc_a1_a_i              ( adc_a1_ai ),
  .alert_i                 ( alert_rsp_i ),
  .alert_o                 ( alert_req_o ),
  .dft_strap_test_i        ( dft_strap_test_i ),
  .lc_dft_en_i             ( lc_dft_en_i ),
  .obs_i                   ( obs ),
  .obs_ctrl_o              ( obs_ctrl_o ),
  .padmux2ast_i            ( padmux2ast_i ),
  .ast2padmux_o            ( ast2padmux_o ),
  .mux_iob_sel_o           ( mux_iob_sel_o ),
  .ast2pad_t0_a_o          ( ast2pad_t0_ao ),
  .ast2pad_t1_a_o          ( ast2pad_t1_ao ),
  .ext_freq_is_96m_i       ( ext_freq_is_96m_i ),
  .all_clk_byp_req_i       ( all_clk_byp_req_i ),
  .io_clk_byp_req_i        ( io_clk_byp_req_i ),
  .clk_osc_byp_i           ( clk_osc_byp ),
  .flash_bist_en_o         ( flash_bist_en_o ),
  .mem_cfg_o               ( mem_cfg_secondary_req ),
  .mem_cfg_i               ( mem_cfg_secondary_rsp ),
  .dft_scan_md_o           ( dft_scan_md_o ),
  .scan_shift_en_o         ( scan_shift_en_o ),
  .scan_reset_n_o          ( scan_reset_no ),
  .intraip_s2p_o           ( intraip_s2p ),
  .intraip_p2s_i           ( intraip_p2s )
);

// Main Domain instantiation
ast_part_primary #(
  .EntropyStreams ( EntropyStreams )
) u_ast_part_primary (
  .tl_i                    ( tl_i ),
  .tl_o                    ( tl_o ),
  .clk_ast_tlul_i          ( clk_ast_tlul_i ),
  .rst_ast_tlul_ni         ( rst_ast_tlul_ni ),
  .init_done_o             ( ast_init_done_o ),
  .rng_en_i                ( rng_en_i ),
  .rng_fips_i              ( rng_fips_i ),
  .rng_val_o               ( rng_val_o ),
  .rng_b_o                 ( rng_b_o ),
  .edn_i                   ( entropy_rsp_i ),
  .edn_o                   ( entropy_req_o ),
  .clk_src_sys_jen_i       ( clk_src_sys_jen_i ),
  .clk_ast_es_i            ( clk_ast_es_i ),
  .rst_ast_es_ni           ( rst_ast_es_ni ),
  .intraip_s2p_i           ( intraip_s2p ),
  .intraip_p2s_o           ( intraip_p2s ),
  // Clock bypass interface
  .clk_ast_ext_i           ( clk_ast_ext_i ),
  .clk_src_sys_en_i        ( clk_src_sys_en_i ),
  .clk_src_io_en_i         ( clk_src_io_en_i ),
  .clk_src_usb_en_i        ( clk_src_usb_en_i ),
  .clk_ast_usb_i           ( clk_ast_usb_i ),
  .rst_ast_usb_ni          ( rst_ast_usb_ni ),
  .io_clk_byp_req_i        ( io_clk_byp_req_i ),
  .all_clk_byp_req_i       ( all_clk_byp_req_i ),
  .ext_freq_is_96m_i       ( ext_freq_is_96m_i ),
  .clk_osc_byp_i           ( clk_osc_byp ),
  .clk_src_sys_o           ( clk_src_sys_o ),
  .clk_src_sys_val_o       ( clk_src_sys_val_o ),
  .clk_src_io_o            ( clk_src_io_o ),
  .clk_src_io_val_o        ( clk_src_io_val_o ),
  .clk_src_io_48m_o        ( clk_src_io_48m_o ),
  .clk_src_usb_o           ( clk_src_usb_o ),
  .clk_src_usb_val_o       ( clk_src_usb_val_o ),
  .io_clk_byp_ack_o        ( io_clk_byp_ack_o ),
  .all_clk_byp_ack_o       ( all_clk_byp_ack_o ),
  .mem_cfg_o               ( mem_cfg_primary_req ),
  .mem_cfg_i               ( mem_cfg_primary_rsp )
);

endmodule : ast
