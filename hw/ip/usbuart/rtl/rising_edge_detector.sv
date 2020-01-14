// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module rising_edge_detector (
  input  logic clk_i,
  input  logic rst_ni,
  input  logic in_i,
  output logic out_o
);

  // Store last value
  logic last_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_last
    if (!rst_ni) begin
      last_q <= 1'b0;
    end else begin
      last_q <= in_i;
    end
  end

  // Detect risign edge
  assign out_o = !last_q && in_i;

endmodule
