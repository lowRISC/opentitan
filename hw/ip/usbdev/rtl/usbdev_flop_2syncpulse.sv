// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Generic double-synchronizer flop followed by pulse generation

module usbdev_flop_2syncpulse #(
  parameter int unsigned Width = 16
) (
  input  logic             clk_i,    // receive clock
  input  logic             rst_ni,
  input  logic [Width-1:0] d,
  output logic [Width-1:0] q
);

  // double-flop synchronizer cell
  logic [Width-1:0] d_sync;
  prim_flop_2sync #(.Width (Width)) prim_flop_2sync (
    .clk_i,
    .rst_ni,
    .d,
    .q (d_sync)
  );

  // delay d_sync by 1 cycle
  logic [Width-1:0] d_sync_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      d_sync_q <= '0;
    end else begin
      d_sync_q <= d_sync;
    end
  end

  // rising edge detection
  assign q = d_sync & ~d_sync_q;

endmodule
