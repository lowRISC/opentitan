// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// adc_ctrl module

`include "prim_assert.sv"

module adc_ctrl
  import adc_ctrl_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
) (
  input clk_i,  //regular core clock for SW config interface
  input clk_aon_i,  //always-on slow clock for internal logic
  input rst_ni,  //power-on hardware reset
  input rst_aon_ni,  //power-on reset for the 200KHz clock(logic)

  //Regster interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  output ast_pkg::adc_ast_req_t adc_o,
  input  ast_pkg::adc_ast_rsp_t adc_i,

  //Inter-module IO
  //AST interface
  //input  [9:0] adc_d,
  //ADC voltage level, each step is 2.148mV(2200mV/1024). It covers 0-2.2V
  //input  adc_d_val,//Valid bit(pulse) for adc_d
  //output logic adc_pd,//Power down ADC(used in deep sleep mode to save power)
  //output logic [1:0] adc_chnsel,
  //channel select for ADC;
  //2'b0 means stop, 2'b01 means first channel, 2'b10 means second channel, 2'b11 ilegal

  //interrupt interface
  output logic intr_debug_cable_o,
  // Debug cable is detected(attached or disconnected); raise the interrupt to CPU

  //pwrmgr interface
  output logic debug_cable_wakeup_o
  //Debug cable is detected; wake up the GSC(CPU) in normal sleep and deep sleep mode
  //input  [2:0] pwr_sts,//3'b001: deep sleep, 3'b010: normal sleep, 3'b100: fully active
);

  adc_ctrl_reg2hw_t reg2hw;
  adc_ctrl_hw2reg_t hw2reg;

  // Alerts
  logic [NumAlerts-1:0] alert_test, alerts;
  assign alert_test = {reg2hw.alert_test.q & reg2hw.alert_test.qe};

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(1'b1)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i (alert_test[i]),
      .alert_req_i  (alerts[0]),
      .alert_ack_o  (),
      .alert_state_o(),
      .alert_rx_i   (alert_rx_i[i]),
      .alert_tx_o   (alert_tx_o[i])
    );
  end

  // Register module
  adc_ctrl_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .clk_aon_i,
    .rst_aon_ni,
    .tl_i(tl_i),
    .tl_o(tl_o),
    .reg2hw(reg2hw),
    .hw2reg(hw2reg),
    .intg_err_o(alerts[0]),
    .devmode_i(1'b1)
  );

  // Instantiate DCD core module
  adc_ctrl_core u_adc_ctrl_core (
    .clk_aon_i(clk_aon_i),
    .rst_aon_ni(rst_aon_ni),
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .reg2hw_i(reg2hw),
    .intr_state_o(hw2reg.intr_state),
    .adc_chn_val_o(hw2reg.adc_chn_val),
    .adc_intr_status_o(hw2reg.adc_intr_status),
    .aon_filter_status_o(hw2reg.filter_status),
    .debug_cable_wakeup_o(debug_cable_wakeup_o),
    .intr_debug_cable_o(intr_debug_cable_o),
    .adc_i(adc_i),
    .adc_o(adc_o)
  );

  // All outputs should be known value after reset
  `ASSERT_KNOWN(IntrDebugCableKnown, intr_debug_cable_o)
  `ASSERT_KNOWN(WakeDebugCableKnown, debug_cable_wakeup_o)
  `ASSERT_KNOWN(TlODValidKnown, tl_o.d_valid)
  `ASSERT_KNOWN(TlOAReadyKnown, tl_o.a_ready)
  `ASSERT_KNOWN(AdcKnown_A, adc_o)
  `ASSERT_KNOWN(AlertsKnown_A, alert_tx_o)

endmodule
