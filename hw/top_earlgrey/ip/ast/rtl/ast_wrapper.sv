// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This is the integration wrapper layer for AST

`include "prim_assert.sv"

module ast_wrapper import ast_wrapper_pkg::*;
(
  // root clock / rests
  input clk_ext_i,
  input por_ni,

  // Bus Interface
  input tlul_pkg::tl_h2d_t bus_i,
  output tlul_pkg::tl_d2h_t bus_o,

  // pwrmgr interface
  input pwrmgr_pkg::pwr_ast_req_t pwr_i,
  output pwrmgr_pkg::pwr_ast_rsp_t pwr_o,

  // rstmgr interface
  output ast_rst_t rst_o,

  // clkmgr interface
  output ast_clks_t clks_o,

  // usb interface
  input usb_ref_pulse_i,
  input usb_ref_val_i,

  // synchronization clocks / rests
  input sensor_ctrl_pkg::ast_aux_t aux_i,

  // adc
  // The adc package definition should eventually be moved to the adc module
  input adc_ast_req_t adc_i,
  output adc_ast_rsp_t adc_o,

  // entropy source interface
  // The entropy source pacakge definition should eventually be moved to es
  input entropy_src_pkg::entropy_src_rng_req_t es_i,
  output entropy_src_pkg::entropy_src_rng_rsp_t es_o,

  // alerts interface
  input ast_alert_rsp_t alert_i,
  output ast_alert_req_t alert_o,

  // assorted ast status
  output ast_status_t status_o
);


  ///////////////////////////
  // AST instantiation
  ///////////////////////////

  // temporary assignments until pwrmgr interface is updated
  assign pwr_o.core_clk_val[0] = ~pwr_o.core_clk_val[1];
  assign pwr_o.slow_clk_val[0] = ~pwr_o.slow_clk_val[1];
  assign pwr_o.io_clk_val[0]   = ~pwr_o.io_clk_val[1];

  ast #(
    .NumIoRails(NumIoRails),
    .EntropyStreams(EntropyStreams),
    .AdcChannels(AdcChannels),
    .AdcDataWidth(AdcDataWidth)
  ) i_ast (
    // ast interface and sync clocks / rests
    .clk_ast_io_i(aux_i.clk_ast_io),
    .clk_ast_sys_i(aux_i.clk_ast_sys),
    .clk_ast_usb_i(aux_i.clk_ast_usb),
    .clk_ast_aon_i(aux_i.clk_ast_aon),
    .rst_ast_io_ni(aux_i.rst_ast_io_n),
    .rst_ast_sys_ni(aux_i.rst_ast_sys_n),
    .rst_ast_usb_ni(aux_i.rst_ast_usb_n),
    .rst_ast_aon_ni(aux_i.rst_ast_aon_n),

    // tlul if
    .tl_i(bus_i),
    .tl_o(bus_o),

    // power related
    .por_ni,
    .vcc_pok_o(rst_o.vcc_pok),
    .aon_pok_o(rst_o.aon_pok),
    .main_pok_o(pwr_o.main_pok),
    .io_pok_o(status_o.io_pok),
    .main_pd_ni(pwr_i.main_pd_n),
    .main_iso_en_i(pwr_i.pwr_clamp),

    // power OK control (for debug only). pok signal follows these inputs
    .vcc_supp_i('0),                          // VCC Supply Test
    .main_supp_i('0),                         // MAIN Supply Test
    .aon_supp_i('0),                          // AON Supply Test
    .io_supp_i('0),                           // IO Rails Supply Test

    // output clocks and associated controls
    .clk_src_sys_o(clks_o.clk_sys),
    .clk_src_sys_val_o(pwr_o.core_clk_val[1]),
    .clk_src_sys_en_i(pwr_i.core_clk_en),
    .clk_src_sys_jen_i(1'b0),                 // need to add function in clkmgr

    .clk_src_aon_o(clks_o.clk_aon),
    .clk_src_aon_val_o(pwr_o.slow_clk_val[1]),
    .clk_src_aon_en_i(pwr_i.slow_clk_en),

    .clk_src_usb_o(clks_o.clk_usb),
    .clk_src_usb_val_o(),                      // need to hookup later
    .clk_src_usb_en_i(1'b1),                   // need to hookup later

    .clk_src_io_o(clks_o.clk_io),
    .clk_src_io_val_o(pwr_o.io_clk_val[1]),
    .clk_src_io_en_i(pwr_i.io_clk_en),

    // input clock and references for calibration
    .clk_ast_ext_i(clk_ext_i),
    .usb_ref_pulse_i,
    .usb_ref_val_i,

    // ADC interface
    .adc_ai('0),                               // need to hookup later
    .adc_chnsel_i(adc_i.channel_sel),
    .adc_pd_i(adc_i.pd),
    .adc_d_o(adc_o.data),
    .adc_d_val_o(adc_o.data_valid),

    // entropy source interface
    .rng_en_i(es_i.rng_enable),
    .rng_ok_o(es_o.rng_ok),
    .rng_b_o(es_o.rng_b),

    // entropy distribution interface - need to hookup later
    .entropy_req_o(),
    .entropy_ack_i('0),
    .entropy_i('0),

    // alerts
    .as_alert_po(alert_o.alerts_p[6]),
    .as_alert_no(alert_o.alerts_n[6]),
    .cg_alert_po(alert_o.alerts_p[5]),
    .cg_alert_no(alert_o.alerts_n[5]),
    .gd_alert_po(alert_o.alerts_p[4]),
    .gd_alert_no(alert_o.alerts_n[4]),
    .ts_alert_hi_po(alert_o.alerts_p[3]),
    .ts_alert_hi_no(alert_o.alerts_n[3]),
    .ts_alert_lo_po(alert_o.alerts_p[2]),
    .ts_alert_lo_no(alert_o.alerts_n[2]),
    .ls_alert_po(alert_o.alerts_p[1]),
    .ls_alert_no(alert_o.alerts_n[1]),
    .ot_alert_po(alert_o.alerts_p[0]),
    .ot_alert_no(alert_o.alerts_n[0]),
    .as_alert_ack_i(alert_i.alerts_ack[6]),
    .cg_alert_ack_i(alert_i.alerts_ack[5]),
    .gd_alert_ack_i(alert_i.alerts_ack[4]),
    .ts_alert_hi_ack_i(alert_i.alerts_ack[3]),
    .ts_alert_lo_ack_i(alert_i.alerts_ack[2]),
    .ls_alert_ack_i(alert_i.alerts_ack[1]),
    .ot_alert_ack_i(alert_i.alerts_ack[0]),
    .as_alert_trig_i(alert_i.alerts_trig[6]),
    .cg_alert_trig_i(alert_i.alerts_trig[5]),
    .gd_alert_trig_i(alert_i.alerts_trig[4]),
    .ts_alert_hi_trig_i(alert_i.alerts_trig[3]),
    .ts_alert_lo_trig_i(alert_i.alerts_trig[2]),
    .ls_alert_trig_i(alert_i.alerts_trig[1]),
    .ot_alert_trig_i(alert_i.alerts_trig[0]),

    // flash interface
    .flash_power_down_h_o(),
    .flash_power_ready_h_o(),

    // pad mux related - DFT
    .ast2padmux_o(),  // DFT_2_IO Output Signals
    .padmux2ast_i('0),  // IO_2_DFT Input Signals

    // usb IO calib
    .usb_io_pu_cal_o() // USB IO Pull-up Calibration Setting
    );


endmodule // ast_wrapper
