// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES high-bandwidth pseudo-random number generator for masking
//
// This module uses multiple parallel LFSRs connected to PRINCE S-Boxes and PRESENT permutations
// to generate pseudo-random data for masking the AES cipher core. The LFSRs can be reseeded using
// an external interface.

///////////////////////////////////////////////////////////////////////////////////////////////////
// IMPORTANT NOTE:                                                                               //
//                                   DO NOT USE THIS BLINDLY!                                    //
//                                                                                               //
// It has not yet been verified that this initial implementation produces pseudo-random numbers  //
// of sufficient quality in terms of uniformity and independence, and that it is indeed sutiable //
// for masking purposes.                                                                         //
///////////////////////////////////////////////////////////////////////////////////////////////////

module aes_prng_masking #(
  parameter  int unsigned Width       = 128 + 32,         // must be divisble by CHUNK_SIZE
  localparam int unsigned CHUNK_SIZE  = 32,               // width of the LFSR primitives
  localparam int unsigned NumChunks   = Width/CHUNK_SIZE, // derived parameter

  parameter  bit          SecAllowForcingMasks  = 0, // Allow forcing masks to 0 using
                                                     // force_zero_masks_i. Useful for SCA only.

  // The chunks must not be initialized to 0. Every chunk should get a different seed.
  parameter logic [NumChunks-1:0][CHUNK_SIZE-1:0] DefaultSeed = {NumChunks{CHUNK_SIZE'(1)}}
) (
  input  logic             clk_i,
  input  logic             rst_ni,

  input  logic             force_zero_masks_i,

  // Connections to AES internals, PRNG consumers
  input  logic             data_update_i,
  output logic [Width-1:0] data_o,
  input  logic             reseed_req_i,
  output logic             reseed_ack_o,

  // Connections to outer world, LFSR reseeding
  output logic             entropy_req_o,
  input  logic             entropy_ack_i,
  input  logic [Width-1:0] entropy_i
);

  logic                                 seed_en;
  logic [NumChunks-1:0][CHUNK_SIZE-1:0] prng_seed;
  logic                                 prng_en;
  logic [NumChunks-1:0][CHUNK_SIZE-1:0] prng_state;
  logic [NumChunks-1:0][CHUNK_SIZE-1:0] sub, perm;
  logic                                 phase_q;

  /////////////
  // Control //
  /////////////

  // The data requests are fed from the LFSRs. Reseed requests take precedence interally to the
  // LFSRs. If there is an outstanding reseed request, the PRNG can keep updating and providing
  // pseudo-random data (using the old seed). If the reseeding is taking place, the LFSRs will
  // provide fresh pseudo-random data (the new seed) in the next cycle anyway. This means the
  // PRNG is always ready to provide new pseudo-random data.

  // Reseed requests are directly forwarded to the external interface.
  assign entropy_req_o = reseed_req_i;
  assign reseed_ack_o  = entropy_ack_i;

  // PRNG control
  assign prng_en = data_update_i;
  // TODO: AES still needs to be connected to the entropy source. Until that happens we don't
  // really reseed the LFSRs to enable initial SCA.
  // See https://github.com/lowRISC/opentitan/issues/1005
  assign seed_en = 1'b0; // entropy_req_o & entropy_ack_i;

  ///////////
  // LFSRs //
  ///////////

  // We use multiple LFSR instances each having a width of CHUNK_SIZE.
  for (genvar c = 0; c < NumChunks; c++) begin : gen_chunks

    // Extract entropy input.
    assign prng_seed[c] = entropy_i[c * CHUNK_SIZE +: CHUNK_SIZE];

    prim_lfsr #(
      .LfsrType    ( "GAL_XOR"      ),
      .LfsrDw      ( CHUNK_SIZE     ),
      .StateOutDw  ( CHUNK_SIZE     ),
      .DefaultSeed ( DefaultSeed[c] )
    ) u_lfsr_chunk (
      .clk_i     ( clk_i         ),
      .rst_ni    ( rst_ni        ),
      .seed_en_i ( seed_en       ),
      .seed_i    ( prng_seed[c]  ),
      .lfsr_en_i ( prng_en       ),
      .entropy_i ( '0            ),
      .state_o   ( prng_state[c] )
    );

    // "Scramble" the LFSR state to break linear shift patterns.
    assign sub[c]  = prim_cipher_pkg::sbox4_32bit(prng_state[c], prim_cipher_pkg::PRINCE_SBOX4);
    assign perm[c] = prim_cipher_pkg::perm_32bit(sub[c], prim_cipher_pkg::PRESENT_PERM32);
  end

  /////////////
  // Outputs //
  /////////////

  // To achieve independence of input and output masks (the output mask of round X is the input
  // mask of round X+1), we assign the scrambled chunks to the output data in alternating fashion.
  assign data_o =
      (SecAllowForcingMasks && force_zero_masks_i) ? '0                             :
       phase_q                                     ? {perm[0], perm[NumChunks-1:1]} : perm;

  if (!SecAllowForcingMasks) begin : gen_unused_force_masks
    logic unused_force_zero_masks;
    assign unused_force_zero_masks = force_zero_masks_i;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_phase
    if (!rst_ni) begin
      phase_q <= '0;
    end else if (prng_en) begin
      phase_q <= ~phase_q;
    end
  end

  /////////////////
  // Asssertions //
  /////////////////

  // Width must be divisible by CHUNK_SIZE
  `ASSERT_INIT(AesPrngMaskingWidth, Width % CHUNK_SIZE == 0)

endmodule
