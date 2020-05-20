// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This is the integration wrapper layer for AST

`include "prim_assert.sv"

module sensor_ctrl import sensor_ctrl_pkg::*; (
  // Primary module clocks
  input clk_i,
  input rst_ni,

  // Bus Interface
  input tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Bus interface to ast
  output ast_bus_req_t ast_bus_o,
  input ast_bus_rsp_t ast_bus_i,

  // Interface from AST
  //input ast_wrapper_pkg::ast_alert_req_t ast_alert_i,
  //output ast_wrapper_pkg::ast_alert_rsp_t ast_alert_o,
  //These interfaces should come from ast eventually
  input ast_alert_req_t ast_alert_i,
  output ast_alert_rsp_t ast_alert_o,
  input ast_status_t ast_status_i,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o

);

  import sensor_ctrl_reg_pkg::*;

  ///////////////////////////
  // Register interface
  ///////////////////////////
  sensor_ctrl_reg2hw_t reg2hw;
  sensor_ctrl_hw2reg_t hw2reg;

  tlul_pkg::tl_h2d_t tl_ast_h2d [1];
  tlul_pkg::tl_d2h_t tl_ast_d2h [1];

  sensor_ctrl_reg_top i_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .tl_win_o(tl_ast_h2d),
    .tl_win_i(tl_ast_d2h),
    .reg2hw,
    .hw2reg,
    .devmode_i(1'b1)
  );

  assign hw2reg.status.d = ast_status_i.io_pok;
  assign hw2reg.status.de = 1'b1;

  // Convert to tlul_adapter_sram for ast access
  logic gnt;

  tlul_adapter_sram #(
    .SramAw(AstAddrBits),
    .SramDw(AstDataBits),
    .ByteAccess(0)
  ) u_to_prog_fifo (
    .clk_i,
    .rst_ni,
    .tl_i       (tl_ast_h2d[0]),
    .tl_o       (tl_ast_d2h[0]),
    .req_o      (ast_bus_o.req_valid),
    .gnt_i      (gnt),
    .we_o       (ast_bus_o.we),
    .addr_o     (ast_bus_o.addr),
    .wmask_o    (),
    .wdata_o    (ast_bus_o.wdata),
    .rdata_i    (ast_bus_i.rdata),
    .rvalid_i   (ast_bus_i.rsp_valid),
    .rerror_i   ('0)
  );

  // Glue logic for creating grant.
  // Only 1 transaction allowed at a time
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      gnt <= 1'b1;
    end else if (!gnt && ast_bus_i.rsp_valid) begin
      gnt <= 1'b1;
    end else if (ast_bus_o.req_valid) begin
      gnt <= 1'b0;
    end
  end

  ///////////////////////////
  // Alert handling
  ///////////////////////////

  logic [NumAlerts-1:0] diff_err;
  logic [NumAlerts-1:0] alerts_vld, alerts_clr;
  logic [NumAlerts-1:0] sw_ack_mode;

  // a particular alert is only valid if differential
  assign alerts_vld = ast_alert_i.alerts_p ^ ast_alert_i.alerts_n;

  // Differential errors are devasting and should never happen.
  // If differential errors are detected, hold state on that permanently until reboot.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      diff_err <= '0;
    end else if (&alerts_vld == '0) begin
      diff_err <= diff_err | ~alerts_vld;
    end
  end

  // fire an alert whenever indicated, or whenever input no longer differential
  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_senders

    // when there is a valid alert, set the alert state
    logic valid_alert;

    assign sw_ack_mode[i] = ast_ack_mode_e'(reg2hw.ack_mode[i].q) == SwAck;

    // if differential checks fail, generate alert
    assign valid_alert = ast_alert_i.alerts_p[i] | diff_err[i];
    assign hw2reg.alert_state[i].d  = sw_ack_mode[i];
    assign hw2reg.alert_state[i].de = valid_alert;

    prim_alert_sender #(
      .AsyncOn(0)
    ) i_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_i(sw_ack_mode[i] ? reg2hw.alert_state[i].q : valid_alert),
      .alert_rx_i(alert_rx_i[i]),
      .alert_tx_o(alert_tx_o[i])
    );

    assign alerts_clr[i] = sw_ack_mode[i] & reg2hw.alert_state[i].q & reg2hw.alert_state[i].qe;
  end

  // When in immediate ack mode, ack alerts as they come
  // When in software ack mode, only ack when software issues the command to clear alert_state
  always_comb begin
    ast_alert_o.alerts_ack = '0;
    for (int i = 0; i < NumAlerts; i++) begin
      if (!sw_ack_mode[i]) begin
        ast_alert_o.alerts_ack[i] = ast_alert_i.alerts_p[i] & alerts_vld[i];
      end else begin
        ast_alert_o.alerts_ack[i] = alerts_clr[i];
      end
    end
  end

endmodule // sensor_ctrl
