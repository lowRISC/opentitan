// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Experiment module implementing multiple galois multiply operations
// Need to see which one has better AT tradeoffs
//

`include "prim_assert.sv"

module flash_xex_mult #(
  parameter int Width = 32,
  // For 32 the positions are (32,15,9,7,4,3,0),
  parameter logic[Width-1:0] IPoly = 1'b1 << 15 |
                        1'b1 << 9 |
                        1'b1 << 7 |
                        1'b1 << 4 |
                        1'b1 << 3 |
                        1'b1 << 0
) (
  input        clk_i,
  input        rst_ni,
  input [Width-1:0] a_i,
  input [Width-1:0] b_i,
  input        start_i,
  output logic done_o,
  output logic [Width-1:0] prod0_o,
  output logic [Width-1:0] prod1_o
);

  logic [Width-1:0][Width-1:0] matrix;
  logic start_int0, start_int1;
  logic start0, start1;
  logic done0, done1;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      start_int0 <= 1'b1;
      start_int1 <= 1'b1;
    end else if (done_o) begin
      start_int0 <= 1'b1;
      start_int1 <= 1'b1;
    end else begin
      start_int0 <= ~done0;
      start_int1 <= ~done1;
    end
  end

  assign start0 = start_i & start_int0;
  assign start1 = start_i & start_int1;

  assign done_o = done0 && done1;

  // This first implementation takes less than 1 cycle once the matrix generation is done
  // so do not allow it to start until then
  flash_gen_matrix #(
    .Width(Width),
    .IPoly(IPoly)
  ) u_gen_matrix (
    .clk_i,
    .rst_ni,
    .start_i(start0),
    .entropy_i('0),
    .seed_i(a_i),
    .done_o(done0),
    .matrix_o(matrix)
  );

  assign prod0_o = flash_ctrl_pkg::mult(matrix, b_i);


  flash_gfmult #(
    .Width(Width),
    .StagesPerCycle(Width/2),
    .IPoly(IPoly)
  ) u_mult2 (
    .clk_i,
    .rst_ni,
    // don't start until the above is done
    .start_i(start1),
    .operand_a_i(a_i),
    .operand_b_i(b_i),
    .done_o(done1),
    .prod_o(prod1_o)
  );

endmodule
