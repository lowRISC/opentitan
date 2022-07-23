// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module accumulates incoming alert triggers. Once the current accumulator
// value is greater or equal the accumulator threshold, the next occurence of
// class_trig_i will trigger escalation.
//
// Note that the accumulator is implemented using a saturation counter which
// does not wrap around.
//

`include "prim_assert.sv"

module alert_handler_accu import alert_pkg::*; (
  input                        clk_i,
  input                        rst_ni,
  input                        class_en_i,   // class enable
  input                        clr_i,        // clear the accumulator
  input                        class_trig_i, // increments the accu
  input        [AccuCntDw-1:0] thresh_i,     // escalation trigger threshold
  output logic [AccuCntDw-1:0] accu_cnt_o,   // output of current accu value
  output logic                 accu_trig_o,  // escalation trigger output
  output logic                 accu_fail_o   // asserted if the tandem accu counters are not equal
);

  logic trig_gated, accu_en;
  assign trig_gated = class_trig_i & class_en_i;
  assign accu_en = trig_gated && !(&accu_cnt_o);

  // SEC_CM: ACCU.CTR.REDUN
  // We employ two redundant counters to guard against FI attacks.
  // If any of the two is glitched and the two counter states do not agree,
  // the check_fail_o signal is asserted which will move the corresponding escalation
  // FSM into a terminal error state where all escalation actions will be permanently asserted.
  prim_count #(
    .Width(AccuCntDw),
    // The alert handler behaves differently than other comportable IP. I.e., instead of sending out
    // an alert signal, this condition is handled internally in the alert handler.
    .EnableAlertTriggerSVA(0)
  ) u_prim_count (
    .clk_i,
    .rst_ni,
    .clr_i,
    .set_i(1'b0),
    .set_cnt_i('0),
    .incr_en_i(accu_en),
    .decr_en_i(1'b0),
    .step_i(AccuCntDw'(1)),
    .cnt_o(accu_cnt_o),
    .cnt_next_o(),
    .err_o(accu_fail_o)
  );

  assign accu_trig_o = (accu_cnt_o >= thresh_i) & trig_gated;

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT(DisabledNoTrigFwd_A, !class_en_i |-> !accu_trig_o)
  `ASSERT(DisabledNoTrigBkwd_A, accu_trig_o |-> class_en_i)
  `ASSERT(CountSaturateStable_A, accu_cnt_o == {AccuCntDw{1'b1}} |=> $stable(accu_cnt_o))
endmodule : alert_handler_accu
