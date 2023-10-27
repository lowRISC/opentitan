// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module aon_timer_core import aon_timer_reg_pkg::*; (
  input  logic                      clk_aon_i,
  input  logic                      rst_aon_ni,

  input  lc_ctrl_pkg::lc_tx_t [2:0] lc_escalate_en_i,
  input  logic                      sleep_mode_i,

  // Register interface
  input  aon_timer_reg2hw_t         reg2hw_i,
  output logic                      wkup_count_reg_wr_o,
  output logic [31:0]               wkup_count_wr_data_o,
  output logic                      wdog_count_reg_wr_o,
  output logic [31:0]               wdog_count_wr_data_o,

  output logic                      wkup_intr_o,
  output logic                      wdog_intr_o,
  output logic                      wdog_reset_req_o
);

  logic        unused_reg2hw;
  // Wakeup signals
  logic [11:0] prescale_count_d, prescale_count_q;
  logic        prescale_en;
  logic        wkup_incr;
  // Watchdog signals
  logic        wdog_incr;

  //////////////////
  // Wakeup Timer //
  //////////////////

  // Prescaler counter
  assign prescale_count_d = wkup_incr ? 12'h000 : (prescale_count_q + 12'h001);
  assign prescale_en      = reg2hw_i.wkup_ctrl.enable.q & (lc_escalate_en_i[0] == lc_ctrl_pkg::Off);

  always_ff @(posedge clk_aon_i or negedge rst_aon_ni) begin
    if (!rst_aon_ni) begin
      prescale_count_q <= 12'h000;
    end else if (prescale_en) begin
      prescale_count_q <= prescale_count_d;
    end
  end

  // Wakeup timer count
  assign wkup_incr = (lc_escalate_en_i[1] == lc_ctrl_pkg::Off) & reg2hw_i.wkup_ctrl.enable.q &
                     (prescale_count_q == reg2hw_i.wkup_ctrl.prescaler.q);

  assign wkup_count_reg_wr_o  = wkup_incr;
  assign wkup_count_wr_data_o = (reg2hw_i.wkup_count.q + 32'd1);

  // Timer interrupt
  assign wkup_intr_o = wkup_incr & (reg2hw_i.wkup_count.q >= reg2hw_i.wkup_thold.q);

  ////////////////////
  // Watchdog Timer //
  ////////////////////

  // Watchdog timer count
  assign wdog_incr = reg2hw_i.wdog_ctrl.enable.q & (lc_escalate_en_i[2] == lc_ctrl_pkg::Off) &
                     ~(sleep_mode_i & reg2hw_i.wdog_ctrl.pause_in_sleep.q);

  assign wdog_count_reg_wr_o  = wdog_incr;
  assign wdog_count_wr_data_o = (reg2hw_i.wdog_count.q + 32'd1);

  // Timer interrupt
  assign wdog_intr_o = wdog_incr & (reg2hw_i.wdog_count.q >= reg2hw_i.wdog_bark_thold.q);
  // Timer reset
  assign wdog_reset_req_o = wdog_incr & (reg2hw_i.wdog_count.q >= reg2hw_i.wdog_bite_thold.q);

  assign unused_reg2hw = |{reg2hw_i.intr_state, reg2hw_i.intr_test, reg2hw_i.wkup_cause,
                           reg2hw_i.alert_test};


endmodule
