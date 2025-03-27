// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module encodes a single bit signal to a differentially encoded signal.
//
// In case the differential pair crosses an asynchronous boundary, it has
// to be re-synchronized to the local clock.

module prim_diff_encode (
  input logic  clk_i,
  input logic  rst_ni,
  // Single line input signal
  input logic  req_i,
  // Output diff pair
  output logic diff_po,
  output logic diff_no
);
  // Buff the input signal to avoid any optimization
  logic req;
  prim_sec_anchor_buf #(
    .Width(1)
  ) u_prim_buf_in_req (
    .in_i(req_i),
    .out_o(req)
  );

  // Differentially encode input
  logic diff_p, diff_n;
  assign diff_p = req;
  assign diff_n = ~req;

  // This prevents further tool optimizations of the differential signal.
  prim_sec_anchor_buf #(
    .Width(2)
  ) u_prim_buf_ack (
    .in_i({diff_n, diff_p}),
    .out_o({diff_n_buf, diff_p_buf})
  );

  // Flop differentially encoded signal at the output
  prim_flop #(
    .Width(1),
    .ResetValue(1'b0)
  ) u_diff_p (
    .clk_i,
    .rst_ni,
    .d_i   ( diff_p_buf ),
    .q_o   ( diff_po    )
  );

  prim_flop #(
    .Width(1),
    .ResetValue(1'b1)
  ) u_diff_n (
    .clk_i,
    .rst_ni,
    .d_i   ( diff_n_buf ),
    .q_o   ( diff_no    )
  );
endmodule : prim_diff_encode
