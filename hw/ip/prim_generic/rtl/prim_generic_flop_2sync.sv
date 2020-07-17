// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Generic double-synchronizer flop
// This may need to be moved to prim_generic if libraries have a specific cell
// for synchronization

module prim_generic_flop_2sync #(
  parameter int Width       = 16,
  localparam int WidthSubOne = Width-1, // temp work around #2679
  parameter logic [WidthSubOne:0] ResetValue = '0
) (
  input                    clk_i,       // receive clock
  input                    rst_ni,
  input        [Width-1:0] d_i,
  output logic [Width-1:0] q_o
);

  logic [Width-1:0] intq;

  prim_flop #(
    .Width(Width),
    .ResetValue(ResetValue)
  ) u_sync_1 (
    .clk_i,
    .rst_ni,
    .d_i,
    .q_o(intq)
  );

  prim_flop #(
    .Width(Width),
    .ResetValue(ResetValue)
  ) u_sync_2 (
    .clk_i,
    .rst_ni,
    .d_i(intq),
    .q_o
  );


endmodule
