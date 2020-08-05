// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Domain-Oriented Masking GF(2) Multiplier with 2-shares
// ref: Higher-Order Side-Channel Protected Implementations of Keccak
//     https://eprint.iacr.org/2017/395.pdf
//
// q0 = a0 & b0 + (a0 & b1 + z)
// q1 = a1 & b1 + (a1 & b0 + z)
// () ==> registered
//
// all input should be stable for two clocks
// as the output is valid after a clock
// For z, it can use other slice from the state
// as it is fairly random w.r.t the current inputs.

// General formula of Q in the paper
// Qi = t{i,i} + Sig(j>i,d)(t{i,j}+Z{i+j*(j-1)/2}) + Sig(j<i,d)(t{i,j}+Z{j+i*(i-1)/2})
// for d=1 (NumShare 2 for first order protection)
// Q0 = t{0,0} + Sig(j>0,1)(t{0,j}+Z{j(j-1)/2}) + Sig(j<0,d)(..)
//    = a0&b0  + (a0&b1 + z0                    + 0)
// Q1 = t{1,1} + sig(j>1,1)(...) + sig(j<1,1)(t{1,j} + Z{j})
//    = a1&b1  + (0              + a1&b0 + z0)

`include "prim_assert.sv"

module prim_dom_and_2share #(
  parameter int DW = 64, // Input width
  parameter int EnNegedge  = 0 // Enable negedge of clk for register
) (
  input clk_i,

  input [DW-1:0] a0_i, // share0 of a
  input [DW-1:0] a1_i, // share1 of a
  input [DW-1:0] b0_i, // share0 of b
  input [DW-1:0] b1_i, // share1 of b
  input [DW-1:0] c0_i, // share0 of random number
  input [DW-1:0] c1_i, // share1 of random number

  output logic [DW-1:0] q0_o, // share0 of q
  output logic [DW-1:0] q1_o  // share1 of q
);

  logic [DW-1:0] t0_d, t0_q, t1_d, t1_q;
  logic [DW-1:0] t_a0b1, t_a1b0, t_a0b0, t_a1b1;
  //synopsys keep_signal_name t_a0b1
  //synopsys keep_signal_name t_a1b0
  //synopsys keep_signal_name t_a0b0
  //synopsys keep_signal_name t_a1b1

  // Preserve the logic sequence for XOR not to preceed the AND
  assign t_a0b1 = a0_i & b1_i;
  assign t_a1b0 = a1_i & b0_i;
  assign t0_d = t_a0b1 ^ c0_i;
  assign t1_d = t_a1b0 ^ c1_i;

  if (EnNegedge == 1) begin: gen_negreg
    always_ff @(negedge clk_i) begin
      t0_q <= t0_d;
      t1_q <= t1_d;
    end
  end else begin: gen_posreg
    always_ff @(posedge clk_i) begin
      t0_q <= t0_d;
      t1_q <= t1_d;
    end
  end

  assign t_a0b0 = a0_i & b0_i;
  assign t_a1b1 = a1_i & b1_i;
  assign q0_o = t_a0b0 ^ t0_q;
  assign q1_o = t_a1b1 ^ t1_q;

  // DOM AND should be same as unmasked computation
  if ( !(EnNegedge == 0)) begin: gen_andchk
    `ASSERT(UnmaskedValue_A, q0_o ^ q1_o == (a0_i ^ a1_i) & (b0_i & b1_i), clk_i, 1'b0)
  end

endmodule

