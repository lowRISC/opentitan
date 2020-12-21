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

`include "prim_assert.sv"

module aes_prng_masking import aes_pkg::*;
#(
  parameter  int unsigned Width     = WidthPRDMasking,     // Must be divisble by ChunkSize and 8.
  parameter  int unsigned ChunkSize = ChunkSizePRDMasking, // width of the LFSR primitives
  localparam int unsigned NumChunks = Width/ChunkSize,     // derived parameter

  parameter  bit          SecAllowForcingMasks  = 0, // Allow forcing masks to 0 using
                                                     // force_zero_masks_i. Useful for SCA only.

  parameter masking_lfsr_seed_t    RndCnstLfsrSeed      = RndCnstMaskingLfsrSeedDefault,
  parameter mskg_chunk_lfsr_perm_t RndCnstChunkLfsrPerm = RndCnstMskgChunkLfsrPermDefault
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

  localparam int unsigned NumBytes  = Width/8;

  logic                                seed_en;
  logic [NumChunks-1:0][ChunkSize-1:0] prng_seed;
  logic                                prng_en;
  logic [NumChunks-1:0][ChunkSize-1:0] prng_state, sub;
  logic            [NumBytes-1:0][7:0] prng_b, sub_b;
  logic                                phase_q;

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

  // We use multiple LFSR instances each having a width of ChunkSize.
  for (genvar c = 0; c < NumChunks; c++) begin : gen_chunks

    // Extract entropy input.
    assign prng_seed[c] = entropy_i[c * ChunkSize +: ChunkSize];

    prim_lfsr #(
      .LfsrType    ( "GAL_XOR"                                   ),
      .LfsrDw      ( ChunkSize                                   ),
      .StateOutDw  ( ChunkSize                                   ),
      .DefaultSeed ( RndCnstLfsrSeed[c * ChunkSize +: ChunkSize] ),
      .StatePermEn ( 1'b1                                        ),
      .StatePerm   ( RndCnstChunkLfsrPerm                        )
    ) u_lfsr_chunk (
      .clk_i     ( clk_i         ),
      .rst_ni    ( rst_ni        ),
      .seed_en_i ( seed_en       ),
      .seed_i    ( prng_seed[c]  ),
      .lfsr_en_i ( prng_en       ),
      .entropy_i ( '0            ),
      .state_o   ( prng_state[c] )
    );
  end

  // Furhter "scramble" the LFSR state at the byte level to break linear shift patterns.
  assign prng_b = prng_state;
  for (genvar b = 0; b < NumBytes; b++) begin : gen_sub
    assign sub_b[b] = prim_cipher_pkg::sbox4_8bit(prng_b[b], prim_cipher_pkg::PRINCE_SBOX4);
  end
  assign sub = sub_b;

  /////////////
  // Outputs //
  /////////////

  // To achieve independence of input and output masks (the output mask of round X is the input
  // mask of round X+1), we assign the scrambled chunks to the output data in alternating fashion.
  assign data_o =
      (SecAllowForcingMasks && force_zero_masks_i) ? '0                           :
       phase_q                                     ? {sub[0], sub[NumChunks-1:1]} : sub;

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

  // Width must be divisible by ChunkSize
  `ASSERT_INIT(AesPrngMaskingWidthByChunk, Width % ChunkSize == 0)
  // Width must be divisible by 8
  `ASSERT_INIT(AesPrngMaskingWidthBy8, Width % 8 == 0)

endmodule
