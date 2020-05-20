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
  input sensor_ctrl_pkg::ast_bus_req_t bus_i,
  output sensor_ctrl_pkg::ast_bus_rsp_t bus_o,

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
  input sensor_ctrl_pkg::ast_intf_t intf_i,

  // adc
  // The adc package definition should eventually be moved to the adc module
  input adc_ast_req_t adc_i,
  output adc_ast_rsp_t adc_o,

  // entropy source interface
  // The entropy source pacakge definition should eventually be moved to es
  input es_ast_req_t es_i,
  output es_ast_rsp_t es_o,

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
    .AdcDataWidth(AdcDataWidth),
    .AstAddrBits(AstAddrBits),
    .AstDataBits(AstDataBits)
  ) i_ast (
    // ast bus interface and sync clocks / rests
    .clk_ast_io_i(intf_i.clk_ast_io),
    .clk_ast_sys_i(intf_i.clk_ast_main),
    .clk_ast_usb_i(intf_i.clk_ast_usb),
    .clk_ast_muxed_i(intf_i.clk_ast_muxed),
    .rst_ast_io_ni(intf_i.rst_ast_io_n),
    .rst_ast_sys_ni(intf_i.rst_ast_main_n),
    .rst_ast_usb_ni(intf_i.rst_ast_usb_n),
    .req_i(bus_i.req_valid),
    .we_i(bus_i.we),
    .addr_i(bus_i.addr),
    .wdata_i(bus_i.wdata),
    .rsp_o(bus_o.rsp_valid),
    .rdata_o(bus_o.rdata),

    // power related
    .por_ni,
    .vcc_pok_o(rst_o.vcc_pok),
    .aon_pok_o(rst_o.aon_pok),
    .main_pok_o(pwr_o.main_pok),
    .io_pok_o(status_o.io_pok),
    .main_pd_ni(pwr_i.main_pd_n),
    .main_iso_en_i(pwr_i.pwr_clamp),

    // output clocks and associated controls
    .sys_clk_o(clks_o.clk_main),
    .sys_clk_val_o(pwr_o.core_clk_val[1]),
    .sys_clk_en_i(pwr_i.core_clk_en),
    .sys_clk_jen_i(1'b0),                 // need to add function in clkmgr

    .aon_clk_o(clks_o.clk_aon),
    .aon_clk_val_o(pwr_o.slow_clk_val[1]),
    .aon_clk_en_i(pwr_i.slow_clk_en),

    .usb_clk_o(clks_o.clk_usb),
    .usb_clk_val_o(),                      // need to hookup later
    .usb_clk_en_i(1'b1),                   // need to hookup later

    .io_clk_o(clks_o.clk_io),
    .io_clk_val_o(pwr_o.io_clk_val[1]),
    .io_clk_en_i(pwr_i.io_clk_en),

    // input clock and references for calibration
    .ext_clk_i(clk_ext_i),
    .usb_ref_pulse_i,
    .usb_ref_val_i,

    // ADC interface
    .ADC_A_i('0),                         // need to hookup later
    .adc_cs_i(adc_i.channel_sel),
    .adc_pd_i(adc_i.pd),
    .adc_d_o(adc_o.data),
    .adc_d_val_o(adc_o.data_valid),

    // entropy source interface - need to get actual names from es module later
    .rng_en_i(es_i.rng_en),
    .rng_ok_o(es_o.rng_ok),
    .rng_b_o(es_o.rng_b),

    // entropy distribution interface
    // TBD

    // alerts
    .as_alert_po(alert_o.alerts_p[0]),
    .as_alert_no(alert_o.alerts_n[0]),
    .cg_alert_po(alert_o.alerts_p[1]),
    .cg_alert_no(alert_o.alerts_n[1]),
    .gd_alert_po(alert_o.alerts_p[2]),
    .gd_alert_no(alert_o.alerts_n[2]),
    .ts_alert_hi_po(alert_o.alerts_p[3]),
    .ts_alert_hi_no(alert_o.alerts_n[3]),
    .ts_alert_lo_po(alert_o.alerts_p[4]),
    .ts_alert_lo_no(alert_o.alerts_n[4]),
    .ls_alert_po(alert_o.alerts_p[5]),
    .ls_alert_no(alert_o.alerts_n[5]),
    .ot_alert_po(alert_o.alerts_p[6]),
    .ot_alert_no(alert_o.alerts_n[6]),
    .as_alert_ack_i(alert_i.alerts_ack[0]),
    .cg_alert_ack_i(alert_i.alerts_ack[1]),
    .gd_alert_ack_i(alert_i.alerts_ack[2]),
    .ts_alert_hi_ack_i(alert_i.alerts_ack[3]),
    .ts_alert_lo_ack_i(alert_i.alerts_ack[4]),
    .ls_alert_ack_i(alert_i.alerts_ack[5]),
    .ot_alert_ack_i(alert_i.alerts_ack[6])
    );


endmodule // ast_wrapper
