// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module accumulates incoming alert triggers. Once the current accumulator
// value is greater or equal the accumulator threshold, the next occurence of
// trig_i will trigger escalation.
//
// Note that the accumulator is implemented using a saturation counter which
// does not wrap around.
//

module alert_handler_accu (
  input                                   clk_i,
  input                                   rst_ni,
  input                                   clr_i,     // clear the accumulator
  input                                   trig_i,    // increments the accu
  input        [alert_pkg::AccuCntDw-1:0] thresh_i,  // escalation trigger threshold
  output logic [alert_pkg::AccuCntDw-1:0] cnt_o,     // output of current accu value
  output logic                            trig_o     // escalation trigger output
);

  logic [alert_pkg::AccuCntDw-1:0] accu_d, accu_q;

  assign accu_d = (clr_i)                ? '0            : // clear
                  (trig_i && !(&accu_q)) ? accu_q + 1'b1 : // saturate counter at maximum
                                           accu_q;

  assign trig_o = (accu_q >= thresh_i) & trig_i;

  assign cnt_o = accu_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      accu_q <= '0;
    end else begin
      accu_q <= accu_d;
    end
  end

endmodule : alert_handler_accu
