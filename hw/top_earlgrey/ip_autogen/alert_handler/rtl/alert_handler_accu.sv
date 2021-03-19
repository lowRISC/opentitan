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

  logic trig_gated_unbuf;
  assign trig_gated_unbuf = class_trig_i & class_en_i;

  // We employ two redundant counters to guard against FI attacks.
  // If any of the two is glitched and the two counter states do not agree,
  // the check_fail_o signal is asserted which will move the corresponding escalation
  // FSM into a terminal error state where all escalation actions will be permanently asserted.
  logic [1:0][AccuCntDw-1:0] accu_q;
  for (genvar k = 0; k < 2; k++) begin : gen_double_accu

    logic trig_gated_buf, clr_buf;
    logic [AccuCntDw-1:0] accu_d;

    // These size_only buffers are instantiated in order to prevent
    // optimization / merging of the two counters.
    prim_buf u_prim_buf_clr (
      .in_i(clr_i),
      .out_o(clr_buf)
    );

    prim_buf u_prim_buf_trig (
      .in_i(trig_gated_unbuf),
      .out_o(trig_gated_buf)
    );

    assign accu_d = (clr_buf)                         ? '0               : // clear
                    (trig_gated_buf && !(&accu_q[k])) ? accu_q[k] + 1'b1 : // saturate counter
                                                        accu_q[k];

    prim_flop #(
      .Width(AccuCntDw)
    ) u_prim_flop (
      .clk_i,
      .rst_ni,
      .d_i(accu_d),
      .q_o(accu_q[k])
    );
  end

  assign accu_cnt_o = accu_q[0];
  assign accu_trig_o = (accu_q[0] >= thresh_i) & trig_gated_unbuf;
  assign accu_fail_o = accu_q[0] != accu_q[1];

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT(DisabledNoTrigFwd_A, !class_en_i |-> !accu_trig_o)
  `ASSERT(DisabledNoTrigBkwd_A, accu_trig_o |-> class_en_i)
  `ASSERT(CheckFailFwd_A, accu_q[0] != accu_q[1] |-> accu_fail_o)
  `ASSERT(CheckFailBkwd_A, accu_fail_o |-> accu_q[0] != accu_q[1])

endmodule : alert_handler_accu
