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
  parameter int DW = 64 // Input width
) (
  input clk_i,
  input rst_ni,

  input [DW-1:0] a0_i, // share0 of a
  input [DW-1:0] a1_i, // share1 of a
  input [DW-1:0] b0_i, // share0 of b
  input [DW-1:0] b1_i, // share1 of b
  input          z_valid_i, // random number input validity
  input [DW-1:0] z_i,  // random number

  output logic [DW-1:0] q0_o, // share0 of q
  output logic [DW-1:0] q1_o  // share1 of q
);

  logic [DW-1:0] t0_d, t0_q, t1_d, t1_q;
  logic [DW-1:0] t_a0b1, t_a1b0, t_a0b0, t_a1b1;

  /////////////////
  // Calculation //
  /////////////////
  // Inner-domain terms
  assign t_a0b0 = a0_i & b0_i;
  assign t_a1b1 = a1_i & b1_i;

  // Cross-domain terms
  assign t_a0b1 = a0_i & b1_i;
  assign t_a1b0 = a1_i & b0_i;

  ///////////////
  // Resharing //
  ///////////////
  // Resharing of cross-domain terms

  // Preserve the logic sequence for XOR not to proceed cross-domain AND.
  prim_xor2 #(
    .Width ( DW*2 )
  ) u_prim_xor_t01 (
    .in0_i ( {t_a0b1, t_a1b0} ),
    .in1_i ( {z_i,    z_i}    ),
    .out_o ( {t0_d,   t1_d}   )
  );

  // Register stage
  prim_flop_en #(
    .Width      ( DW*2 ),
    .ResetValue ( '0   )
  ) u_prim_flop_t01 (
    .clk_i  ( clk_i        ),
    .rst_ni ( rst_ni       ),
    .en_i   ( z_valid_i    ),
    .d_i    ( {t0_d, t1_d} ),
    .q_o    ( {t0_q, t1_q} )
  );

  /////////////////
  // Integration //
  /////////////////

  // Preserve the logic sequence for XOR not to proceed the inner-domain AND.
  prim_xor2 #(
    .Width ( DW*2 )
  ) u_prim_xor_q01 (
    .in0_i ( {t_a0b0, t_a1b1} ),
    .in1_i ( {t0_q,   t1_q}   ),
    .out_o ( {q0_o,   q1_o}   )
  );

  // DOM AND should be same as unmasked computation
  // TODO: Put assumption that input need to be stable for at least two cycles
  // The correct test sequence will be:
  //   1. inputs are changed
  //   2. check if z_valid_i,
  //   3. at the next cycle, inputs are still stable (assumption)
  //   4. and results Q == A & B (assertion)

  // To speed up the FPV process, random value is ready in less than or
  // equal to two cycles.
  `ASSUME_FPV(RandomReadyInShortTime_A,
    $changed(a0_i) || $changed(a1_i) || $changed(b0_i) || $changed(b1_i)
      |-> ##[0:2] z_valid_i,
    clk_i, !rst_ni)
  `ASSERT(UnmaskedAndMatched_A,
    $changed(a0_i) || $changed(a1_i) || $changed(b0_i) || $changed(b1_i)
      |-> ##[0:$] z_valid_i
      |=> $stable(a0_i) && $stable(a1_i) && $stable(b0_i) && $stable(b1_i)
      |-> (q0_o ^ q1_o) == ((a0_i ^ a1_i) & (b0_i ^ b1_i)),
    clk_i, !rst_ni)

endmodule

