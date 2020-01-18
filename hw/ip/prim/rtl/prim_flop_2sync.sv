// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Generic double-synchronizer flop

module prim_flop_2sync #(
  parameter int Width      = 16,
  parameter bit ResetValue = 0
) (
  input                    clk_i,    // receive clock
  input                    rst_ni,
  input        [Width-1:0] d,
  output logic [Width-1:0] q
);

  logic [Width-1:0] intq;

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      intq <= {Width{ResetValue}};
      q    <= {Width{ResetValue}};
    end else begin
      intq <= d;
      q    <= intq;
    end

endmodule
