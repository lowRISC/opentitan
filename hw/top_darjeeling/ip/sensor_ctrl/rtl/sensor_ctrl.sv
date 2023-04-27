// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This is the integration wrapper layer for AST

`include "prim_assert.sv"

module sensor_ctrl
  import sensor_ctrl_pkg::*;
  import sensor_ctrl_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
) (
  // Primary module clocks
  input clk_i,
  input rst_ni,
  input clk_aon_i,
  input rst_aon_ni,

  // Bus Interface
  input tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // Interface from AST
  input ast_pkg::ast_alert_req_t ast_alert_i,
  output ast_pkg::ast_alert_rsp_t ast_alert_o,
  input ast_pkg::ast_status_t ast_status_i,
  input [ast_pkg::Ast2PadOutWidth-1:0] ast2pinmux_i,
  input prim_mubi_pkg::mubi4_t ast_init_done_i,

  // Interface to pinmux
  output logic [ast_pkg::Ast2PadOutWidth-1:0] cio_ast_debug_out_o,
  output logic [ast_pkg::Ast2PadOutWidth-1:0] cio_ast_debug_out_en_o,

  // Interrutps
  output logic intr_io_status_change_o,
  output logic intr_init_status_change_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // wakeup to power manager
  output logic wkup_req_o
);

  // The reg_pkg number of alerts and ast alerts must always match
  `ASSERT_INIT(NumAlertsMatch_A, ast_pkg::NumAlerts == NumAlertEvents)

  ///////////////////////////
  // Incoming event synchronization - alerts can assert asynchronously
  ///////////////////////////
  logic [NumAlertEvents-1:0] async_alert_event_p, alert_event_p;
  logic [NumAlertEvents-1:0] async_alert_event_n, alert_event_n;

  for (genvar i = 0; i < NumAlertEvents; i++) begin : gen_alert_sync_assign
    prim_sec_anchor_buf #(
      .Width(2)
    ) u_alert_in_buf (
      .in_i({ast_alert_i.alerts[i].p,
             ast_alert_i.alerts[i].n}),
      .out_o({async_alert_event_p[i],
              async_alert_event_n[i]})
    );
  end

  prim_flop_2sync #(
    .Width(NumAlertEvents),
    .ResetValue('0)
  ) u_alert_p_sync (
    .clk_i,
    .rst_ni,
    .d_i(async_alert_event_p),
    .q_o(alert_event_p)
  );

  prim_flop_2sync #(
    .Width(NumAlertEvents),
    .ResetValue({NumAlertEvents{1'b1}})
  ) u_alert_n_sync (
    .clk_i,
    .rst_ni,
    .d_i(async_alert_event_n),
    .q_o(alert_event_n)
  );


  ///////////////////////////
  // Register interface
  ///////////////////////////
  sensor_ctrl_reg2hw_t reg2hw;
  sensor_ctrl_hw2reg_t hw2reg;
  logic intg_err;

  sensor_ctrl_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .intg_err_o(intg_err),
    .devmode_i(1'b1)
  );

  ///////////////////////////
  // Interrupt handling
  ///////////////////////////

  // io status change
  logic [NumIoRails-1:0] io_rise;
  logic [NumIoRails-1:0] io_fall;
  prim_edge_detector #(
    .Width(NumIoRails),
    .EnSync(1)
  ) u_io_status_chg (
    .clk_i,
    .rst_ni,
    .d_i(ast_status_i.io_pok),
    .q_sync_o(hw2reg.status.io_pok.d),
    .q_posedge_pulse_o(io_rise),
    .q_negedge_pulse_o(io_fall)
  );

  assign hw2reg.status.io_pok.de = 1'b1;

  prim_intr_hw #(.Width(1)) u_io_intr (
    .clk_i,
    .rst_ni,
    .event_intr_i           (|{io_rise, io_fall}),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.io_status_change.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.io_status_change.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.io_status_change.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.io_status_change.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.io_status_change.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.io_status_change.d),
    .intr_o                 (intr_io_status_change_o)
  );

  // init_done change
  logic init_rise;
  logic init_fall;
  prim_edge_detector #(
    .Width(1),
    .EnSync(1)
  ) u_init_chg (
    .clk_i,
    .rst_ni,
    .d_i(prim_mubi_pkg::mubi4_test_true_strict(ast_init_done_i)),
    .q_sync_o(hw2reg.status.ast_init_done.d),
    .q_posedge_pulse_o(init_rise),
    .q_negedge_pulse_o(init_fall)
  );

  prim_intr_hw #(.Width(1)) u_init_intr (
    .clk_i,
    .rst_ni,
    .event_intr_i           (|{init_rise, init_fall}),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.init_status_change.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.init_status_change.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.init_status_change.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.init_status_change.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.init_status_change.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.init_status_change.d),
    .intr_o                 (intr_init_status_change_o)
  );

  assign hw2reg.status.ast_init_done.de = 1'b1;

  ///////////////////////////
  // Alert Event Handling
  ///////////////////////////

  logic [NumAlertEvents-1:0] event_vld, event_clr;

  // While the alerts are differential, they are not perfectly aligned.
  // Instead, each alert is treated independently.
  always_comb begin
    for (int i = 0; i < NumAlertEvents; i++) begin
      event_vld[i] = alert_event_p[i] | ~alert_event_n[i];
    end
  end

  // Only recoverable alerts are ack'd.  Fatal alerts are captured and continuously
  // triggered, there is thus not a need to ever acknowledge the source.
  // For recoverable alerts, the ack is only sent once the alert is captured into software readable
  // registers
  logic [NumAlertEvents-1:0] recov_event;
  logic [NumAlertEvents-1:0] fatal_event;
  for (genvar i = 0; i < NumAlertEvents; i++) begin : gen_ast_alert_events

    // when there is a valid alert, set the alert state
    assign recov_event[i] = event_vld[i] & ~reg2hw.fatal_alert_en[i];
    assign fatal_event[i] = event_vld[i] & reg2hw.fatal_alert_en[i];

    assign hw2reg.recov_alert[i].d  = 1'b1;
    assign hw2reg.recov_alert[i].de = recov_event[i];

    assign hw2reg.fatal_alert[i].d  = 1'b1;
    assign hw2reg.fatal_alert[i].de = fatal_event[i];

    // only recoverable alerts ack
    assign event_clr[i] = recov_event[i] & reg2hw.recov_alert[i].q;

  end

  // handle internal alert events, currently only have fatals
  for (genvar i = NumAlertEvents; i < TotalEvents; i++) begin : gen_local_alert_events
    assign hw2reg.fatal_alert[i].d  = 1'b1;
    assign hw2reg.fatal_alert[i].de = intg_err;
  end

  // Note, even though the incoming alerts are differential, they are NOT expected to be
  // consistent all the time.  It is more appropriate for sensor_ctrl to treat them as
  // independent lines.
  // As a result, the alert_ack is only applied if an incoming alert is set to the active polarity.
  //

  always_comb begin
    for (int i = 0; i < NumAlertEvents; i++) begin
      ast_alert_o.alerts_ack[i].p = alert_event_p[i] & event_clr[i];
      ast_alert_o.alerts_ack[i].n = ~(~alert_event_n[i] & event_clr[i]);
    end
  end

  // alert trigger for test
  always_comb begin
    for (int i = 0; i < NumAlertEvents; i++) begin
      ast_alert_o.alerts_trig[i].p = reg2hw.alert_trig[i];
      ast_alert_o.alerts_trig[i].n = ~reg2hw.alert_trig[i];
    end
  end


  // alert test connection
  logic [NumAlerts-1:0] alert_test;
  assign alert_test[RecovAlert] = reg2hw.alert_test.recov_alert.qe &
                                  reg2hw.alert_test.recov_alert.q;
  assign alert_test[FatalAlert] = reg2hw.alert_test.fatal_alert.qe &
                                  reg2hw.alert_test.fatal_alert.q;

  prim_alert_sender #(
    .AsyncOn(AlertAsyncOn[RecovAlert]),
    .IsFatal(0)
  ) u_prim_recov_alert_sender (
    .clk_i,
    .rst_ni,
    .alert_test_i(alert_test[RecovAlert]),
    .alert_req_i(|recov_event),
    .alert_ack_o(),
    .alert_state_o(),
    .alert_rx_i(alert_rx_i[RecovAlert]),
    .alert_tx_o(alert_tx_o[RecovAlert])
  );

  prim_alert_sender #(
    .AsyncOn(AlertAsyncOn[FatalAlert]),
    .IsFatal(1)
  ) u_prim_fatal_alert_sender (
    .clk_i,
    .rst_ni,
    .alert_test_i(alert_test[FatalAlert]),
    .alert_req_i(|reg2hw.fatal_alert),
    .alert_ack_o(),
    .alert_state_o(),
    .alert_rx_i(alert_rx_i[FatalAlert]),
    .alert_tx_o(alert_tx_o[FatalAlert])
  );

  ///////////////////////////
  // wakeup generation
  ///////////////////////////

  // wakeups are synchronized separately from the normal event handling.
  // The alert handling is not synchronized through these below because
  // the ack latency would be very long for no apparent gain.

  logic async_wake;
  logic unstable_wake_req;

  // async wake combines ast inputs as well as recoverable alerts.
  // This is because it is possible for alert events to arrive "right"
  // on the boundary of low power. In the event this happens, the
  // original event is immediately 'acked', making it possible for the
  // sync flops below to miss the event. By mixing in recov_alert,
  // we guarantee that if the event is caught by the regfile, it can also
  // be used to trigger wake from low power.
  // Fatal alerts are not used here because they do not ever ack, meaning
  // the originating event can never disappear.
  assign async_wake = (|async_alert_event_p)  |
                      (~&async_alert_event_n) |
                      (|reg2hw.recov_alert);

  prim_flop_2sync #(
    .Width(1),
    .ResetValue('0)
  ) u_wake_sync (
    .clk_i,
    .rst_ni,
    .d_i(async_wake),
    .q_o(unstable_wake_req)
  );

  logic [2:0] wake_req_filter;
  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni) begin
      wake_req_filter <= '0;
    end else begin
      wake_req_filter <= {wake_req_filter[1:0], unstable_wake_req};
    end
  end

  // The filter is needed since the input is purely combinational
  // among async events.  The filter is thus used to ensure the
  // wake indication is real and not a glitch.
  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni) begin
      wkup_req_o <= '0;
    end else begin
      wkup_req_o <= &wake_req_filter;
    end
  end

  ///////////////////////////
  // pinmux feedthrough to ast
  ///////////////////////////

  assign cio_ast_debug_out_o = ast2pinmux_i;
  assign cio_ast_debug_out_en_o = '1;

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[FatalAlert])
endmodule // sensor_ctrl
