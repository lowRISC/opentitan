// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module encodes a single bit signal to a differentially encoded signal.
//
// In case the differential pair crosses an asynchronous boundary, it has
// to be re-synchronized to the local clock.

module prim_diff_encode (
  input        clk_i,
  input        rst_ni,
  // Single line input signal
  input         req_i,
  // Output diff pair
  output logic  diff_po,
  output logic  diff_no
);
  logic diff_p, diff_n;

  // Differntially encode input
  assign diff_p = req_i;
  assign diff_n = ~req_i;

  // Flop differentially encoded signal at the output
  prim_flop #(
    .Width(1),
    .ResetValue(1'b0)
  ) u_diff_p (
    .clk_i,
    .rst_ni,
    .d_i   ( diff_p  ),
    .q_o   ( diff_po )
  );

  prim_flop #(
    .Width(1),
    .ResetValue(1'b1)
  ) u_diff_n (
    .clk_i,
    .rst_ni,
    .d_i   ( diff_n  ),
    .q_o   ( diff_no )
  );
endmodule : prim_diff_encode
