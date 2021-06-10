// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

`include "prim_assert.sv"

module aon_timer (
  input  logic                clk_i,
  input  logic                clk_aon_i,
  input  logic                rst_ni,
  input  logic                rst_aon_ni,

  // TLUL interface on clk_i domain
  input  tlul_pkg::tl_h2d_t   tl_i,
  output tlul_pkg::tl_d2h_t   tl_o,

  // clk_i domain
  input  lc_ctrl_pkg::lc_tx_t lc_escalate_en_i,
  output logic                intr_wkup_timer_expired_o,
  output logic                intr_wdog_timer_bark_o,

  // clk_aon_i domain
  output logic                aon_timer_wkup_req_o,
  output logic                aon_timer_rst_req_o,

  // async domain
  input  logic                sleep_mode_i
);

  import aon_timer_reg_pkg::*;

  localparam int AON_WKUP = 0;
  localparam int AON_WDOG = 1;

  // TLUL structs
  tlul_pkg::tl_h2d_t         tl_aon_h2d;
  tlul_pkg::tl_d2h_t         tl_aon_d2h;
  // Register structs
  aon_timer_reg2hw_t         aon_reg2hw;
  aon_timer_hw2reg_t         aon_hw2reg;
  // Register write signals
  logic                      wkup_count_reg_wr;
  logic [31:0]               wkup_count_wr_data;
  logic                      wdog_count_reg_wr;
  logic [31:0]               wdog_count_wr_data;
  // Other sync signals
  lc_ctrl_pkg::lc_tx_t [2:0] lc_escalate_en;
  // Interrupt signals
  logic                      aon_wkup_intr_set;
  logic                      aon_wdog_intr_set;
  logic [1:0]                intr_aon_test_q;
  logic                      intr_aon_test_qe;
  logic [1:0]                intr_aon_state_q;
  logic                      intr_aon_state_de;
  logic [1:0]                intr_aon_state_d;
  logic [1:0]                intr_out;
  // Reset signals
  logic                      aon_rst_req_set;
  logic                      aon_rst_req_d, aon_rst_req_q;

  //////////////////////////////
  // Register Write Interface //
  //////////////////////////////

  assign aon_hw2reg.wkup_count.de = wkup_count_reg_wr;
  assign aon_hw2reg.wkup_count.d  = wkup_count_wr_data;
  assign aon_hw2reg.wdog_count.de = wdog_count_reg_wr;
  assign aon_hw2reg.wdog_count.d  = wdog_count_wr_data;

  // registers instantiation
  aon_timer_reg_top u_reg (
    .clk_i      (clk_aon_i),
    .rst_ni     (rst_aon_ni),

    .tl_i       (tl_aon_h2d),
    .tl_o       (tl_aon_d2h),

    .reg2hw     (aon_reg2hw),
    .hw2reg     (aon_hw2reg),

    .intg_err_o (),
    .devmode_i  (1'b1)
  );

  ///////////////////////////////////////
  // Sync TLUL signals into AON Domain //
  ///////////////////////////////////////

  tlul_fifo_async #(
      .ReqDepth (1), // There will only ever be 1 req outstanding from the core
      .RspDepth (1)
  ) u_tlul_fifo (
      .clk_h_i    (clk_i),
      .rst_h_ni   (rst_aon_ni), // keep pointers consistent by using single reset
      .clk_d_i    (clk_aon_i),
      .rst_d_ni   (rst_aon_ni),
      .tl_h_i     (tl_i),
      .tl_h_o     (tl_o),
      .tl_d_o     (tl_aon_h2d),
      .tl_d_i     (tl_aon_d2h)
  );

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

  logic sleep_mode;
  prim_flop_2sync #(
    .Width(1)
  ) u_sync_sleep_mode (
    .clk_i   (clk_aon_i),
    .rst_ni  (rst_aon_ni),
    .d_i     (sleep_mode_i),
    .q_o     (sleep_mode)
  );

  aon_timer_core u_core (
    .clk_aon_i,
    .rst_aon_ni,
    .sleep_mode_i              (sleep_mode),
    .lc_escalate_en_i          (lc_escalate_en),
    .reg2hw_i                  (aon_reg2hw),
    .wkup_count_reg_wr_o       (wkup_count_reg_wr),
    .wkup_count_wr_data_o      (wkup_count_wr_data),
    .wdog_count_reg_wr_o       (wdog_count_reg_wr),
    .wdog_count_wr_data_o      (wdog_count_wr_data),
    .wkup_intr_o               (aon_wkup_intr_set),
    .wdog_intr_o               (aon_wdog_intr_set),
    .wdog_reset_req_o          (aon_rst_req_set)
  );

  ////////////////////
  // Wakeup Signals //
  ////////////////////

  // Wakeup request is set by HW and cleared by SW
  assign aon_hw2reg.wkup_cause.de = (aon_wkup_intr_set | aon_wdog_intr_set) & sleep_mode;
  assign aon_hw2reg.wkup_cause.d  = 1'b1;

  assign aon_timer_wkup_req_o = aon_reg2hw.wkup_cause.q;

  ////////////////////////
  // Interrupt Handling //
  ////////////////////////

  // Registers to interrupt
  assign intr_aon_test_qe           = aon_reg2hw.intr_test.wkup_timer_expired.qe |
                                      aon_reg2hw.intr_test.wdog_timer_expired.qe;
  assign intr_aon_test_q [AON_WKUP] = aon_reg2hw.intr_test.wkup_timer_expired.q;
  assign intr_aon_state_q[AON_WKUP] = aon_reg2hw.intr_state.wkup_timer_expired.q;
  assign intr_aon_test_q [AON_WDOG] = aon_reg2hw.intr_test.wdog_timer_expired.q;
  assign intr_aon_state_q[AON_WDOG] = aon_reg2hw.intr_state.wdog_timer_expired.q;

  // Interrupts to registers
  assign aon_hw2reg.intr_state.wkup_timer_expired.d  = intr_aon_state_d[AON_WKUP];
  assign aon_hw2reg.intr_state.wkup_timer_expired.de = intr_aon_state_de;
  assign aon_hw2reg.intr_state.wdog_timer_expired.d  = intr_aon_state_d[AON_WDOG];
  assign aon_hw2reg.intr_state.wdog_timer_expired.de = intr_aon_state_de;

  prim_intr_hw #(
    .Width (2)
  ) u_intr_hw (
    .clk_i                  (clk_aon_i),
    .rst_ni                 (rst_aon_ni),
    .event_intr_i           ({aon_wdog_intr_set, aon_wkup_intr_set}),

    .reg2hw_intr_enable_q_i (2'b11),
    .reg2hw_intr_test_q_i   (intr_aon_test_q),
    .reg2hw_intr_test_qe_i  (intr_aon_test_qe),
    .reg2hw_intr_state_q_i  (intr_aon_state_q),
    .hw2reg_intr_state_de_o (intr_aon_state_de),
    .hw2reg_intr_state_d_o  (intr_aon_state_d),

    .intr_o                 (intr_out)
  );

  prim_flop_2sync #(
    .Width(1)
  ) u_sync_wkup_intr (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),
    .d_i     (intr_out[AON_WKUP]),
    .q_o     (intr_wkup_timer_expired_o)
  );

  prim_flop_2sync #(
    .Width(1)
  ) u_sync_wdog_intr (
    .clk_i   (clk_i),
    .rst_ni  (rst_ni),
    .d_i     (intr_out[AON_WDOG]),
    .q_o     (intr_wdog_timer_bark_o)
  );

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
  `ASSERT_KNOWN(IntrWkupKnown_A, intr_wkup_timer_expired_o)
  `ASSERT_KNOWN(IntrWdogKnown_A, intr_wdog_timer_bark_o)
  // clk_aon_i domain
  `ASSERT_KNOWN(WkupReqKnown_A, aon_timer_wkup_req_o, clk_aon_i, !rst_aon_ni)
  `ASSERT_KNOWN(RstReqKnown_A, aon_timer_rst_req_o, clk_aon_i, !rst_aon_ni)

endmodule
