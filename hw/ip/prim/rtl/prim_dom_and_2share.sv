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
  parameter bit Pipeline = 1'b0 // Enable full pipelining
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
  output logic [DW-1:0] q1_o, // share1 of q
  output logic [DW-1:0] prd_o // pseudo-random data for other instances
);

  logic [DW-1:0] t0_d, t0_q, t1_d, t1_q;
  logic [DW-1:0] t_a0b0, t_a1b1;
  logic [DW-1:0] t_a0b0_d, t_a1b1_d;
  logic [DW-1:0] t_a0b1, t_a1b0;

  /////////////////
  // Calculation //
  /////////////////
  // Inner-domain terms
  assign t_a0b0_d = a0_i & b0_i;
  assign t_a1b1_d = a1_i & b1_i;

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

  /////////////////////////
  // Optional Pipelining //
  /////////////////////////

  if (Pipeline == 1'b1) begin : gen_inner_domain_regs
    // Add pipeline registers on inner-domain terms prior to integration. This allows accepting new
    // input data every clock cycle and prevents SCA leakage occurring due to the integration of
    // reshared cross-domain terms with inner-domain terms derived from different input data.

    logic [DW-1:0] t_a0b0_q, t_a1b1_q;
    prim_flop_en #(
      .Width      ( DW*2 ),
      .ResetValue ( '0   )
    ) u_prim_flop_tab01 (
      .clk_i  ( clk_i                ),
      .rst_ni ( rst_ni               ),
      .en_i   ( z_valid_i            ),
      .d_i    ( {t_a0b0_d, t_a1b1_d} ),
      .q_o    ( {t_a0b0_q, t_a1b1_q} )
    );

    assign t_a0b0 = t_a0b0_q;
    assign t_a1b1 = t_a1b1_q;

  end else begin : gen_no_inner_domain_regs
    // Do not add the optional pipeline registers on the inner-domain terms. This allows to save
    // some area in case the multiplier does not need to accept new data in every cycle. However,
    // this can cause SCA leakage as during the clock cycle in which new data arrives, the new
    // inner-domain terms are integrated with the previous, reshared cross-domain terms.

    assign t_a0b0 = t_a0b0_d;
    assign t_a1b1 = t_a1b1_d;
  end

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

  // Use intermediate results for remasking computations in another instance in the following
  // clock cycle. Use one share only. Directly use output of flops updating with z_valid_i.
  // t1_q is obtained by remasking t_a1b0 with z_i. Since z_i is uniformly distributed and
  // independent of a1/b0_i, t1_q is also uniformly distributed and independent of a1/b0_i.
  // For details, see Lemma 1 in Canright, "A very compact 'perfectly masked' S-box for AES
  // (corrected)" available at https://eprint.iacr.org/2009/011.pdf
  assign prd_o = t1_q;

  // DOM AND should be same as unmasked computation
  // The correct test sequence will be:
  //   1. inputs are changed
  //   2. check if z_valid_i,
  //   3. at the next cycle, inputs are still stable (assumption) - only in case Pipeline = 0
  //   4. and results Q == A & B (assertion)

  // To speed up the FPV process, random value is ready in less than or
  // equal to two cycles.
  `ASSUME_FPV(RandomReadyInShortTime_A,
    $changed(a0_i) || $changed(a1_i) || $changed(b0_i) || $changed(b1_i)
      |-> ##[0:2] z_valid_i,
    clk_i, !rst_ni)

  if (Pipeline == 0) begin: g_assert_stable
    // If Pipeline is not set, the computation takes two cycles without flop
    // crossing the domain. In this case, the signal should be stable for at
    // least two cycles.
    `ASSUME(StableTwoCycles_M,
      ($changed(a0_i)  || $changed(a1_i) || $changed(b0_i) || $changed(b1_i))
        ##[0:$] z_valid_i |=>
        $stable(a0_i) && $stable(a1_i) && $stable(b0_i) && $stable(b1_i))
  end

  `ASSERT(UnmaskedAndMatched_A,
    z_valid_i |=> (q0_o ^ q1_o) ==
      (($past(a0_i) ^ $past(a1_i)) & ($past(b0_i) ^ $past(b1_i))),
    clk_i, !rst_ni)

endmodule
