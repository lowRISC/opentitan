// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This is the integration wrapper layer for AST

`include "prim_assert.sv"

module sensor_ctrl import sensor_ctrl_pkg::*; #(
  parameter logic AlertAsyncOn = 1'b1
) (
  // Primary module clocks
  input clk_i,
  input rst_ni,

  // Bus Interface
  input tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Interface from AST
  input ast_pkg::ast_alert_req_t ast_alert_i,
  output ast_pkg::ast_alert_rsp_t ast_alert_o,
  input ast_pkg::ast_status_t ast_status_i,
  input [ast_pkg::Ast2PadOutWidth-1:0] ast2pinmux_i,
  output logic [ast_pkg::Pad2AstInWidth-1:0] pinmux2ast_o,

  // Interface to pinmux
  input [ast_pkg::Pad2AstInWidth-1:0] cio_ast_debug_in_i,
  output logic [ast_pkg::Ast2PadOutWidth-1:0] cio_ast_debug_out_o,
  output logic [ast_pkg::Ast2PadOutWidth-1:0] cio_ast_debug_out_en_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o

);


  ///////////////////////////
  // Register interface
  ///////////////////////////
  import sensor_ctrl_reg_pkg::*;
  sensor_ctrl_reg2hw_t reg2hw;
  sensor_ctrl_hw2reg_t hw2reg;

  sensor_ctrl_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .intg_err_o(),
    .devmode_i(1'b1)
  );

  assign hw2reg.status.d = ast_status_i.io_pok;
  assign hw2reg.status.de = 1'b1;


  ///////////////////////////
  // Alert handling
  ///////////////////////////

  logic [NumAlerts-1:0] alert_test;
  logic [NumAlerts-1:0] alerts_vld, alerts_clr;
  logic [NumAlerts-1:0] sw_ack_mode;
  logic [NumAlerts-1:0] no_ack_mode;

  // While the alerts are differential, they are not perfectly aligned.
  // Instead, each alert is treated independently.
  always_comb begin
    for (int i = 0; i < NumAlerts; i++) begin
      alerts_vld[i] = ast_alert_i.alerts[i].p | ~ast_alert_i.alerts[i].n;
    end
  end

  // alert test connection
  assign alert_test[AsSel]   = reg2hw.alert_test.recov_as.qe    & reg2hw.alert_test.recov_as.q;
  assign alert_test[CgSel]   = reg2hw.alert_test.recov_cg.qe    & reg2hw.alert_test.recov_cg.q;
  assign alert_test[GdSel]   = reg2hw.alert_test.recov_gd.qe    & reg2hw.alert_test.recov_gd.q;
  assign alert_test[TsHiSel] = reg2hw.alert_test.recov_ts_hi.qe & reg2hw.alert_test.recov_ts_hi.q;
  assign alert_test[TsLoSel] = reg2hw.alert_test.recov_ts_lo.qe & reg2hw.alert_test.recov_ts_lo.q;
  assign alert_test[LsSel]   = reg2hw.alert_test.recov_ls.qe    & reg2hw.alert_test.recov_ls.q;
  assign alert_test[OtSel]   = reg2hw.alert_test.recov_ot.qe    & reg2hw.alert_test.recov_ot.q;


  // fire an alert whenever indicated
  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_senders

    // when there is a valid alert, set the alert state
    logic valid_alert;

    assign sw_ack_mode[i] = ast_ack_mode_e'(reg2hw.ack_mode[i].q) == SwAck;
    assign no_ack_mode[i] = ast_ack_mode_e'(reg2hw.ack_mode[i].q) == NoAck |
                            ast_ack_mode_e'(reg2hw.ack_mode[i].q) == InvalidAck;

    // if differential checks fail, generate alert
    assign valid_alert = alerts_vld[i];
    assign hw2reg.alert_state[i].d  = sw_ack_mode[i];
    assign hw2reg.alert_state[i].de = valid_alert;

    logic alert_req;
    logic alert_ack;
    assign alert_req = sw_ack_mode[i] ? reg2hw.alert_state[i].q : valid_alert;

    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn),
      .IsFatal(0)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i(alert_test[i]),
      .alert_req_i(alert_req),
      .alert_ack_o(alert_ack),
      .alert_state_o(),
      .alert_rx_i(alert_rx_i[i]),
      .alert_tx_o(alert_tx_o[i])
    );

    assign alerts_clr[i] = no_ack_mode[i] ? '0 :
                           sw_ack_mode[i] ? ~reg2hw.alert_state[i].q & reg2hw.alert_state[i].qe :
                                            alert_req & alert_ack;
  end

  // When in immediate ack mode, ack alerts as they are received by the sender
  // When in software ack mode, only ack when software issues the command to clear alert_state
  //
  // Note, even though the incoming alerts are differential, they are NOT expected to be
  // consistent all the time.  It is more appropriate for sensor_ctrl to treat them as
  // independent lines.
  // As a result, the alerts_clr is only applied if an incoming alert is set to the active polarity.
  //
  // Note, due to the converging nature of sensor ctrl (non-synced inputs being forwarded to 1
  // alert), it is possible that when one alert arrives, it is ack'd right when the differential
  // version comes.  As a result, the first alert will be ack'd, and the second will also
  // immediately be ack'd, resulting in one alert being sent.
  // This is OK because the intent is to send the alert anyways, and the ack would not have happened
  // if the alert was not sent out.  If the incoming alert stays high, then alerts will continue to
  // fire.
  always_comb begin
    for (int i = 0; i < NumAlerts; i++) begin
      ast_alert_o.alerts_ack[i].p = ast_alert_i.alerts[i].p & alerts_clr[i];
      ast_alert_o.alerts_ack[i].n = ~(~ast_alert_i.alerts[i].n & alerts_clr[i]);
    end
  end

  // alert trigger for test
  always_comb begin
    for (int i = 0; i < NumAlerts; i++) begin
      ast_alert_o.alerts_trig[i].p = reg2hw.alert_trig[i];
      ast_alert_o.alerts_trig[i].n = ~reg2hw.alert_trig[i];
    end
  end

  ///////////////////////////
  // pinmux feedthrough to ast
  ///////////////////////////

  assign cio_ast_debug_out_o = ast2pinmux_i;
  assign cio_ast_debug_out_en_o = '1;
  assign pinmux2ast_o = cio_ast_debug_in_i;


endmodule // sensor_ctrl
