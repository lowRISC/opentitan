// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Primitive counter-based input filter, with enable.
// Configurable number of cycles. Cheaper version of filter for
// large values of #Cycles
//
// when in reset, stored value is zero
// when enable is false, output is input
// when enable is true, output is stored value,
//   new input must be opposite value from stored value for
//   #Cycles before switching to new value.

module prim_filter_ctr #(
  // If this parameter is set, an additional 2-stage synchronizer will be
  // added at the input.
  parameter bit AsyncOn = 0,
  parameter int unsigned Cycles = 4
) (
  input  clk_i,
  input  rst_ni,
  input  enable_i,
  input  filter_i,
  output filter_o
);

  localparam int unsigned CTR_WIDTH = $clog2(Cycles);
  localparam logic [CTR_WIDTH-1:0] CYCLESM1 = (CTR_WIDTH)'(Cycles-1);

  logic [CTR_WIDTH-1:0] diff_ctr_q, diff_ctr_d;
  logic filter_q, stored_value_q, update_stored_value;

  logic filter_synced;

  if (AsyncOn) begin : gen_async
    // Run this through a 2 stage synchronizer to
    // prevent metastability.
    prim_flop_2sync #(
      .Width(1)
    ) prim_flop_2sync (
      .clk_i,
      .rst_ni,
      .d_i(filter_i),
      .q_o(filter_synced)
    );
  end else begin : gen_sync
    assign filter_synced = filter_i;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      filter_q <= 1'b0;
    end else begin
      filter_q <= filter_synced;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      stored_value_q <= 1'b0;
    end else if (update_stored_value) begin
      stored_value_q <= filter_synced;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      diff_ctr_q <= '0;
    end else begin
      diff_ctr_q <= diff_ctr_d;
    end
  end

  // always look for differences, even if not filter enabled
  assign update_stored_value = (diff_ctr_d == CYCLESM1);
  assign diff_ctr_d = (filter_synced != filter_q) ? '0                   : // restart
                      (diff_ctr_q == CYCLESM1)    ? CYCLESM1             : // saturate
                                                    (diff_ctr_q + 1'b1);   // count up

  assign filter_o = enable_i ? stored_value_q : filter_synced;

endmodule

