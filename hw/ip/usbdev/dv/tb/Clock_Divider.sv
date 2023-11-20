// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module Clock_Divider
(
  input wire clk,
  output bit clk_out
);

  bit [1:0] count=0;

  always @(posedge clk) begin
    count <= count+1;
  end

  always_comb begin
    clk_out = count[1];
  end
endmodule
