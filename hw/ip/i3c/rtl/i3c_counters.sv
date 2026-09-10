// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Counts a number of infrequent events, such as Controller Errors (CEx) and Target Errors (TEx).
//
// - when events occur simultaneously the counters are incremented sequentially so there may be a
//   delay of a few cycles. Since these are error events they should not be frequent.

module i3c_counters #(
  // Number of counters implemented.
  parameter int unsigned Counters = 4,
  // Width of each counter, in bits.
  parameter int unsigned CntW = 8,
  // Whether each input event is indicated by a rising edge.
  parameter logic [Counters-1:0] EdgeTrig = 0
) (
  // Clock and reset.
  input  clk_i,
  input  rst_ni,

  // Input events (count rising edges).
  input  [Counters-1:0] event_i,

  // Current counter values.
  input  [Counters-1:0][CntW-1:0] cnt_q_i,
  // Write strobes to counters.
  output           [Counters-1:0] cnt_de_o,
  // New counter values, saturated.
  output [Counters-1:0][CntW-1:0] cnt_d_o
);

  // Channel all level-sensitive signals through edge detectors.
  logic [Counters-1:0] ev_new;
  for (genvar c = 0; c < Counters; c++) begin : gen_ev_new
    if (EdgeTrig[c]) begin : gen_ev_from_level
      logic event_q;
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) event_q <= 1'b0;
        else event_q <= event_i[c];
      end
      assign ev_new[c] = event_i[c] & !event_q;
    end else begin : gen_ev_from_edge
      assign ev_new[c] = event_i[c];  // Single-cycle pulse input already.
    end
  end

  // Sticky event bits.
  logic [Counters-1:0] ev_sticky;
  // Clear bits once handled.
  logic [Counters-1:0] ev_clear;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) ev_sticky <= 'b0;
    else if (|{ev_new, ev_clear}) ev_sticky <= (ev_sticky & ~ev_clear) | ev_new;
  end
  // This selects the Least Significant set Bit.
  assign ev_clear = ev_sticky & ~(ev_sticky - 'b1);

  // Increment the least significant counter that has seen an event.
  // - we share this logic amongst all counters since there may be many counters but they increment
  //   very infrequently; errors are not expected to occur in normal operation.
  logic [CntW-1:0] cnt_sat, cnt;
  always_comb begin : gen_cnt
    cnt = '0;
    for (int unsigned c = 0; c < Counters; c++) cnt |= {CntW{ev_clear[c]}} & cnt_q_i[c];
  end

  // Emit the saturated count.
  assign cnt_de_o = ev_clear;
  assign cnt_sat  = cnt + ~&cnt;  // Saturate at the maximum representable value.
  assign cnt_d_o  = {Counters{cnt_sat}};

endmodule
