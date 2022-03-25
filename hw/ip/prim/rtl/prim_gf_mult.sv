// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module performs a the multiplication of two operands in Galois field GF(2^Width) modulo the
// provided irreducible polynomial using a parallel Mastrovito multipler [3]. To cut long paths
// potentially occurring for large data widths, the implementation provides a parameter
// StagesPerCycle to decompose the multiplication into Width/StagesPerCycle iterative steps
// (Digit-Serial/Parallel Multiplier [4]).
//
// Note that this module is not pipelined and produces an output sample every Width/StagesPerCycle
// cycles.
//
// References:
//
// [1] Patel, "Parallel Multiplier Designs for the Galois/Counter Mode of Operation",
// https://pdfs.semanticscholar.org/1246/a9ad98dc0421ccfc945e6529c886f23e848d.pdf
// [2] Wagner, "The Laws of Cryptography: The Finite Field GF(2^8)",
// http://www.cs.utsa.edu/~wagner/laws/FFM.html
//
// [3]: Mastrovito, "VLSI Designs for Multiplication over Finite Fields GF(2^m)",
// https://link.springer.com/chapter/10.1007/3-540-51083-4_67
// [4]: Song et al., "Efficient Finite Field Serial/Parallel Multiplication",
// https://ieeexplore.ieee.org/document/542803


`include "prim_assert.sv"

module prim_gf_mult #(
  parameter int Width = 32,
  parameter int StagesPerCycle = Width,

  // The field-generating, irreducible polynomial of degree Width.
  // Can for example be a Conway polynomial, see
  // http://www.math.rwth-aachen.de/~Frank.Luebeck/data/ConwayPol/CP2.html
  // For Width = 33, the Conway polynomial has bits 32, 15, 9, 7, 4, 3, 0 set to one.
  parameter logic[Width-1:0] IPoly = Width'(1'b1) << 15 |
                                     Width'(1'b1) << 9  |
                                     Width'(1'b1) << 7  |
                                     Width'(1'b1) << 4  |
                                     Width'(1'b1) << 3  |
                                     Width'(1'b1) << 0
) (
  input clk_i,
  input rst_ni,
  input req_i,
  input [Width-1:0] operand_a_i,
  input [Width-1:0] operand_b_i,
  output logic ack_o,
  output logic [Width-1:0] prod_o
);

  `ASSERT_INIT(IntegerLoops_A, (Width % StagesPerCycle) == 0)
  `ASSERT_INIT(StagePow2_A, $onehot(StagesPerCycle))

  localparam int Loops = Width / StagesPerCycle;
  localparam int CntWidth = (Loops == 1) ? 1 : $clog2(Loops);

  // reformat operand_b_i
  logic [Loops-1:0][StagesPerCycle-1:0] reformat_data;

  // this slice of operand bits used during each loop
  logic [StagesPerCycle-1:0] op_i_slice;

  // the matrix is made up of a series of GF(2^Width) * x
  logic [StagesPerCycle-1:0][Width-1:0] matrix;

  // since the matrix generation is not done in one go, we must remember
  // where it last left off
  logic [Width-1:0] vector;

  // this variable tracks which loop we are currently operating
  logic [CntWidth-1:0] cnt;

  // this variable tracks the first loop through the multiply
  logic first;

  // intermediate prod held between loops
  logic [Width-1:0] prod_q, prod_d;

  // select current slice
  assign reformat_data = operand_b_i;
  assign op_i_slice = reformat_data[cnt];

  assign first = cnt == 0;

  if (StagesPerCycle == Width) begin : gen_all_combo

    assign ack_o = 1'b1;
    assign cnt = '0;
    assign prod_q = '0;
    assign vector = '0;

  end else begin : gen_decomposed

    // multiply is done
    assign ack_o = int'(cnt) == (Loops - 1);

    // advance the stage count and also advance the bit position count
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        cnt <= '0;
      end else if (req_i && ack_o) begin
        cnt <= '0;
      end else if (req_i && int'(cnt) < (Loops - 1)) begin
        cnt <= cnt + 1'b1;
      end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        prod_q <= '0;
        vector <= '0;
      end else if (ack_o) begin
        prod_q <= '0;
        vector <= '0;
      end else if (req_i) begin
        prod_q <= prod_d;
        vector <= matrix[StagesPerCycle-1];
      end
    end
  end


  assign matrix = first ? gen_matrix(operand_a_i, 1'b1) : gen_matrix(vector, 1'b0);
  assign prod_d = prod_q ^ gf_mult(matrix, op_i_slice);

  // The output is not toggled until it is ready
  assign prod_o = ack_o ? prod_d : operand_a_i;


  // GF(2^Width) * x
  function automatic logic [Width-1:0] gf_mult2(
    logic [Width-1:0] operand
  );
    logic [Width-1:0] mult_out;
    mult_out = operand[Width-1] ? (operand << 1) ^ IPoly : (operand << 1);
    return mult_out;
  endfunction

  // Matrix generate step
  function automatic logic [StagesPerCycle-1:0][Width-1:0] gen_matrix(
    logic [Width-1:0] seed,
    logic init
  );
    logic [StagesPerCycle-1:0][Width-1:0] matrix_out;

    matrix_out[0] = init ? seed : gf_mult2(seed);
    matrix_out[StagesPerCycle-1:1] = '0;
    for (int i = 1; i < StagesPerCycle; i++) begin
      matrix_out[i] = gf_mult2(matrix_out[i-1]);
    end
    return matrix_out;
  endfunction

  // Galois multiply step
  function automatic logic [Width-1:0] gf_mult(
    logic [StagesPerCycle-1:0][Width-1:0] matrix_,
    logic [StagesPerCycle-1:0] operand
  );
    logic [Width-1:0] mult_out;
    logic [Width-1:0] add_vector;
    mult_out = '0;
    for (int i = 0; i < StagesPerCycle; i++) begin
      add_vector = operand[i] ? matrix_[i] : '0;
      mult_out = mult_out ^ add_vector;
    end
    return mult_out;
  endfunction // gf_mult

endmodule // prim_gf_mult
