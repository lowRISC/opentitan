// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module prim_xilinx_clock_buf #(
  parameter bit NoFpgaBuf = 1'b0
) (
  input clk_i,
  output logic clk_o
);

  if (NoFpgaBuf) begin : gen_no_fpga_buf
    assign clk_o = clk_i;
  end else begin : gen_fpga_buf
    BUFG bufg_i (
      .I(clk_i),
      .O(clk_o)
    );
  end


endmodule
