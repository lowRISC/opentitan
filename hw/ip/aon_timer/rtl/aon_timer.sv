// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

`include "prim_assert.sv"

module aon_timer import aon_timer_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
) (
  input  logic                clk_i,
  input  logic                clk_aon_i,
  input  logic                rst_ni,
  input  logic                rst_aon_ni,

  // TLUL interface on clk_i domain
  input  tlul_pkg::tl_h2d_t   tl_i,
  output tlul_pkg::tl_d2h_t   tl_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // clk_i domain
  input  lc_ctrl_pkg::lc_tx_t lc_escalate_en_i,
  output logic                intr_wkup_timer_expired_o,
  output logic                intr_wdog_timer_bark_o,
  output logic                nmi_wdog_timer_bark_o,

  // clk_aon_i domain
  output logic                wkup_req_o,
  output logic                aon_timer_rst_req_o,

  // async domain
  input  logic                sleep_mode_i
);

  localparam int AON_WKUP = 0;
  localparam int AON_WDOG = 1;

  // Register structs
  aon_timer_reg2hw_t         reg2hw;
  aon_timer_hw2reg_t         hw2reg;
  // Register write signals
  logic                      aon_wkup_count_reg_wr;
  logic [31:0]               aon_wkup_count_wr_data;
  logic                      aon_wdog_count_reg_wr;
  logic [31:0]               aon_wdog_count_wr_data;
  // Other sync signals
  lc_ctrl_pkg::lc_tx_t [2:0] lc_escalate_en;
  // Interrupt signals
  logic                      aon_wkup_intr_set;
  logic                      aon_wdog_intr_set;
  logic [1:0]                intr_test_q;
  logic                      intr_test_qe;
  logic [1:0]                intr_state_q;
  logic                      intr_state_de;
  logic [1:0]                intr_state_d;
  logic [1:0]                intr_out;
  // Reset signals
  logic                      aon_rst_req_set;
  logic                      aon_rst_req_d, aon_rst_req_q;
  // Alert signals
  logic [NumAlerts-1:0]      alert_test, alerts;

  //////////////////////////////
  // Register Write Interface //
  //////////////////////////////

  logic aon_sleep_mode;
  prim_flop_2sync #(
    .Width(1)
  ) u_sync_sleep_mode (
    .clk_i   (clk_aon_i),
    .rst_ni  (rst_aon_ni),
    .d_i     (sleep_mode_i),
    .q_o     (aon_sleep_mode)
  );

  assign hw2reg.wkup_count.de = aon_wkup_count_reg_wr;
  assign hw2reg.wkup_count.d  = aon_wkup_count_wr_data;
  assign hw2reg.wdog_count.de = aon_wdog_count_reg_wr;
  assign hw2reg.wdog_count.d  = aon_wdog_count_wr_data;

  // registers instantiation
  aon_timer_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .clk_aon_i,
    .rst_aon_ni,

    .tl_i,
    .tl_o,

    .reg2hw,
    .hw2reg,

    // SEC_CM: BUS.INTEGRITY
    .intg_err_o (alerts[0]),
    .devmode_i  (1'b1)
  );

  ////////////
  // Alerts //
  ////////////

  assign alert_test = {
    reg2hw.alert_test.q &
    reg2hw.alert_test.qe
  };

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(1'b1)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alerts[0]     ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end

  // Lifecycle sync
  prim_lc_sync #(
    .NumCopies(3)
  ) u_lc_sync_escalate_en (
    .clk_i   (clk_aon_i),
    .rst_ni  (rst_aon_ni),
    .lc_en_i (lc_escalate_en_i),
    .lc_en_o (lc_escalate_en)
  );

  ////////////////
  // Timer Core //
  ////////////////

  aon_timer_core u_core (
    .clk_aon_i,
    .rst_aon_ni,
    .sleep_mode_i              (aon_sleep_mode),
    .lc_escalate_en_i          (lc_escalate_en),
    .reg2hw_i                  (reg2hw),
    .wkup_count_reg_wr_o       (aon_wkup_count_reg_wr),
    .wkup_count_wr_data_o      (aon_wkup_count_wr_data),
    .wdog_count_reg_wr_o       (aon_wdog_count_reg_wr),
    .wdog_count_wr_data_o      (aon_wdog_count_wr_data),
    .wkup_intr_o               (aon_wkup_intr_set),
    .wdog_intr_o               (aon_wdog_intr_set),
    .wdog_reset_req_o          (aon_rst_req_set)
  );

  ////////////////////
  // Wakeup Signals //
  ////////////////////

  // Wakeup request is set by HW and cleared by SW
  // The wakeup cause is always captured and only sent out when the system has entered sleep mode
  assign hw2reg.wkup_cause.de = aon_wkup_intr_set | aon_wdog_intr_set;
  assign hw2reg.wkup_cause.d  = 1'b1;

  // cause register resides in AON domain.
  assign wkup_req_o = reg2hw.wkup_cause.q;

  // The wakeup signal is not latched in the pwrmgr so must be held until acked by software
  `ASSERT(WkupStable_A, wkup_req_o |=> wkup_req_o ||
      $fell(reg2hw.wkup_cause.q) && !aon_sleep_mode, clk_aon_i, !rst_aon_ni)

  ////////////////////////
  // Interrupt Handling //
  ////////////////////////

  logic [1:0] aon_intr_set, intr_set;

  prim_flop #(
    .Width      (2),
    .ResetValue (2'b 00)
  ) u_aon_intr_flop (
    .clk_i  (clk_aon_i),
    .rst_ni (rst_aon_ni),
    .d_i    ({aon_wdog_intr_set, aon_wkup_intr_set}),
    .q_o    (aon_intr_set)
  );

  prim_edge_detector #(
    .Width      (2),
    .ResetValue (2'b 00),
    .EnSync     (1'b 1)
  ) u_intr_sync (
    .clk_i,
    .rst_ni,
    .d_i               (aon_intr_set),
    .q_sync_o          (),
    .q_posedge_pulse_o (intr_set),
    .q_negedge_pulse_o ()
  );

  // Registers to interrupt
  assign intr_test_qe           = reg2hw.intr_test.wkup_timer_expired.qe |
                                  reg2hw.intr_test.wdog_timer_bark.qe;
  assign intr_test_q [AON_WKUP] = reg2hw.intr_test.wkup_timer_expired.q;
  assign intr_state_q[AON_WKUP] = reg2hw.intr_state.wkup_timer_expired.q;
  assign intr_test_q [AON_WDOG] = reg2hw.intr_test.wdog_timer_bark.q;
  assign intr_state_q[AON_WDOG] = reg2hw.intr_state.wdog_timer_bark.q;

  // Interrupts to registers
  assign hw2reg.intr_state.wkup_timer_expired.d  = intr_state_d[AON_WKUP];
  assign hw2reg.intr_state.wkup_timer_expired.de = intr_state_de;
  assign hw2reg.intr_state.wdog_timer_bark.d  = intr_state_d[AON_WDOG];
  assign hw2reg.intr_state.wdog_timer_bark.de = intr_state_de;

  prim_intr_hw #(
    .Width (2)
  ) u_intr_hw (
    .clk_i,
    .rst_ni,
    .event_intr_i           (intr_set),
    .reg2hw_intr_enable_q_i (2'b11),
    .reg2hw_intr_test_q_i   (intr_test_q),
    .reg2hw_intr_test_qe_i  (intr_test_qe),
    .reg2hw_intr_state_q_i  (intr_state_q),
    .hw2reg_intr_state_de_o (intr_state_de),
    .hw2reg_intr_state_d_o  (intr_state_d),

    .intr_o                 (intr_out)
  );

  assign intr_wkup_timer_expired_o = intr_out[AON_WKUP];
  assign intr_wdog_timer_bark_o = intr_out[AON_WDOG];

  // The interrupt line can be routed as nmi as well.
  assign nmi_wdog_timer_bark_o = intr_wdog_timer_bark_o;

  ///////////////////
  // Reset Request //
  ///////////////////

  // Once set, the reset request remains asserted until the next aon reset
  assign aon_rst_req_d = aon_rst_req_set | aon_rst_req_q;

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni) begin
      aon_rst_req_q <= 1'b0;
    end else begin
      aon_rst_req_q <= aon_rst_req_d;
    end
  end

  assign aon_timer_rst_req_o = aon_rst_req_q;

  /////////////////////////////
  // Assert Known on Outputs //
  /////////////////////////////

  // clk_i domain
  `ASSERT_KNOWN(TlODValidKnown_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlOAReadyKnown_A, tl_o.a_ready)
  `ASSERT_KNOWN(AlertsKnown_A, alert_tx_o)
  `ASSERT_KNOWN(IntrWkupKnown_A, intr_wkup_timer_expired_o)
  `ASSERT_KNOWN(IntrWdogKnown_A, intr_wdog_timer_bark_o)
  // clk_aon_i domain
  `ASSERT_KNOWN(WkupReqKnown_A, wkup_req_o, clk_aon_i, !rst_aon_ni)
  `ASSERT_KNOWN(RstReqKnown_A, aon_timer_rst_req_o, clk_aon_i, !rst_aon_ni)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_reg, alert_tx_o[0])
endmodule
