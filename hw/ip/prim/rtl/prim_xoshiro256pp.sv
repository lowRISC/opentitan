// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This module implements XoShiRo256++ PRNG
//
// Additional Entropy input to XOR fresh entropy into the state.
// Lockup protection that reseeds the generator if it falls into the all-zero state.
//
// Refs: [1] D. Blackman and S. Vigna, Scrambled Linear Pseudorndom Number Generators
//           https://arxiv.org/pdf/1805.01407.pdf
//       [2] https://prng.di.unimi.it/
//       [3] https://en.wikipedia.org/wiki/Xorshift#xoshiro_and_xoroshiro

`include "prim_assert.sv"

module prim_xoshiro256pp #(
  // Output width, must be a multiple of 64
  parameter int unsigned       OutputDw       = 64,
  // PRNG reset state, must be nonzero!
  parameter logic [255:0]      DefaultSeed    = 256'(1'b1),

  parameter int unsigned NumStages = OutputDw / 64 // derived parameter
) (
  input  logic                  clk_i,
  input  logic                  rst_ni,
  input  logic                  seed_en_i,    // load external seed into the state
  input  logic [255:0]          seed_i,       // external seed input
  input  logic                  xoshiro_en_i, // enables the PRNG
  input  logic [255:0]          entropy_i,    // additional entropy to be XOR'ed into the state
  output logic [OutputDw-1:0]   data_o,       // PRNG output
  output logic                  all_zero_o   // alert signal indicates the all-zero state
);

  logic [255:0] unrolled_state [NumStages+1];
  logic [63:0] mid [NumStages];

  logic lockup;
  logic [255:0] xoshiro_d, xoshiro_q, next_xoshiro_state;

  function automatic logic [255:0] state_update (input logic [255:0] data_in);
    logic [63:0] a_in, b_in, c_in, d_in;
    logic [63:0] a_out, b_out, c_out, d_out;
    a_in = data_in[255:192];
    b_in = data_in[191:128];
    c_in = data_in[127:64];
    d_in = data_in[63:0];
    a_out = a_in ^ b_in ^ d_in;
    b_out = a_in ^ b_in ^ c_in;
    c_out = a_in ^ (b_in << 17) ^ c_in;
    d_out = {d_in[18:0], d_in[63:19]} ^ {b_in[18:0], b_in[63:19]};
    return {a_out, b_out, c_out, d_out};
  endfunction: state_update

  assign unrolled_state[0] = xoshiro_q;

  for (genvar k = 0; k < NumStages; k++) begin : gen_state_functions
    // State update function
    assign unrolled_state[k+1] = state_update(unrolled_state[k]);
    // State output function
    assign mid[k] = unrolled_state[k][255:192] + unrolled_state[k][63:0];
    assign data_o[(k+1)*64-1:k*64] = {mid[k][40:0], mid[k][63:41]} + unrolled_state[k][255:192];
  end

  assign next_xoshiro_state = entropy_i ^ unrolled_state[NumStages];
  assign xoshiro_d = (seed_en_i)              ? seed_i             :
                     (xoshiro_en_i && lockup) ? DefaultSeed        :
                     (xoshiro_en_i)           ? next_xoshiro_state : xoshiro_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_reg_state
    if (!rst_ni) begin
      xoshiro_q <= DefaultSeed;
    end else begin
      xoshiro_q <= xoshiro_d;
    end
  end

  // lockup condition is all-zero
  assign lockup = ~(|xoshiro_q);

  // Indicate that the state is all zeros.
  assign all_zero_o = lockup;

  // check that seed is not all-zero
  `ASSERT_INIT(DefaultSeedNzCheck_A, |DefaultSeed)

endmodule
