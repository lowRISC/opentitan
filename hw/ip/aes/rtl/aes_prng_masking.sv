// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// AES high-bandwidth pseudo-random number generator for masking
//
// This module uses multiple parallel LFSRs each one of them followed by an aligned permutation, a
// non-linear layer (PRINCE S-Boxes) and another permutation layer spanning across all LFSRs to
// generate pseudo-random data for masking the AES cipher core. The LFSRs can be reseeded using an
// external interface.

///////////////////////////////////////////////////////////////////////////////////////////////////
// IMPORTANT NOTE:                                                                               //
//                                   DO NOT USE THIS BLINDLY!                                    //
//                                                                                               //
// This implementation has been experimentally evaluated with / optimized for the masked AES     //
// cipher core using the S-Box implementation with first-order domain-oriented masking.          //
// Other masking schemes and S-Box implementations might have different requirements on the PRNG //
// in terms of uniformity and independence of the generated pseudo-random numbers. Upon changes  //
// to these parts of the design, it is thus recommended to again perform experimental            //
// evaluation. Use with care.                                                                    //
///////////////////////////////////////////////////////////////////////////////////////////////////

`include "prim_assert.sv"

module aes_prng_masking import aes_pkg::*;
#(
  parameter  int unsigned Width        = WidthPRDMasking,     // Must be divisble by ChunkSize and 8
  parameter  int unsigned ChunkSize    = ChunkSizePRDMasking, // Width of the LFSR primitives
  parameter  int unsigned EntropyWidth = edn_pkg::ENDPOINT_BUS_WIDTH,
  parameter  bit          SecAllowForcingMasks  = 0, // Allow forcing masks to constant values using
                                                     // force_masks_i. Useful for SCA only.
  parameter  bit          SecSkipPRNGReseeding  = 0, // The current SCA setup doesn't provide
                                                     // sufficient resources to implement the
                                                     // infrastructure required for PRNG reseeding.
                                                     // To enable SCA resistance evaluations, we
                                                     // need to skip reseeding requests.

  localparam int unsigned NumChunks = Width/ChunkSize, // derived parameter

  parameter masking_lfsr_seed_t RndCnstLfsrSeed = RndCnstMaskingLfsrSeedDefault,
  parameter masking_lfsr_perm_t RndCnstLfsrPerm = RndCnstMaskingLfsrPermDefault
) (
  input  logic                    clk_i,
  input  logic                    rst_ni,

  input  logic                    force_masks_i,

  // Connections to AES internals, PRNG consumers
  input  logic                    data_update_i,
  output logic        [Width-1:0] data_o,
  input  logic                    reseed_req_i,
  output logic                    reseed_ack_o,

  // Connections to outer world, LFSR reseeding
  output logic                    entropy_req_o,
  input  logic                    entropy_ack_i,
  input  logic [EntropyWidth-1:0] entropy_i
);

  logic                [NumChunks-1:0] prng_seed_en;
  logic [NumChunks-1:0][ChunkSize-1:0] prng_seed;
  logic                                prng_en;
  logic [NumChunks-1:0][ChunkSize-1:0] prng_state, perm;
  logic                    [Width-1:0] prng_b, perm_b;
  logic                                phase_q;

  /////////////
  // Control //
  /////////////

  // The data requests are fed from the LFSRs. Reseed requests take precedence internally to the
  // LFSRs. If there is an outstanding reseed request, the PRNG can keep updating and providing
  // pseudo-random data (using the old seed). If the reseeding is taking place, the LFSRs will
  // provide fresh pseudo-random data (the new seed) in the next cycle anyway. This means the
  // PRNG is always ready to provide new pseudo-random data.

  // In the current SCA setup, we don't have sufficient resources to implement the infrastructure
  // required for PRNG reseeding (CSRNG, EDN, etc.). Therefore, we skip any reseeding requests if
  // the SecSkipPRNGReseeding parameter is set. Performing the reseeding without proper entropy
  // provided from CSRNG would result in quickly repeating, fully deterministic PRNG output,
  // which prevents meaningful SCA resistance evaluations.

  // Create a lint error to reduce the risk of accidentally enabling this feature.
  `ASSERT_STATIC_LINT_ERROR(AesSecAllowForcingMasksNonDefault, SecAllowForcingMasks == 0)

  if (SecAllowForcingMasks == 0) begin : gen_unused_force_masks
    logic unused_force_masks;
    assign unused_force_masks = force_masks_i;
  end

  // PRNG control
  assign prng_en = (SecAllowForcingMasks && force_masks_i) ? 1'b0 : data_update_i;

  // Create a lint error to reduce the risk of accidentally enabling this feature.
  `ASSERT_STATIC_LINT_ERROR(AesSecSkipPRNGReseedingNonDefault, SecSkipPRNGReseeding == 0)

  // Width adaption for reseeding interface. We get EntropyWidth bits at a time.
  if (ChunkSize == EntropyWidth) begin : gen_counter
    // We can reseed chunk by chunk as we get fresh entropy. Need to keep track of which chunk to
    // reseed next.
    localparam int unsigned ChunkIdxWidth = prim_util_pkg::vbits(NumChunks);
    logic [ChunkIdxWidth-1:0] chunk_idx_d, chunk_idx_q;
    logic                     prng_reseed_done;

    // Stop requesting entropy once every chunk got reseeded.
    assign entropy_req_o = SecSkipPRNGReseeding ? 1'b0         : reseed_req_i;
    assign reseed_ack_o  = SecSkipPRNGReseeding ? reseed_req_i : prng_reseed_done;

    // Counter
    assign prng_reseed_done =
        (chunk_idx_q == ChunkIdxWidth'(NumChunks - 1)) & entropy_req_o & entropy_ack_i;
    assign chunk_idx_d = prng_reseed_done ? '0                              :
        entropy_req_o && entropy_ack_i    ? chunk_idx_q + ChunkIdxWidth'(1) : chunk_idx_q;

    always_ff @(posedge clk_i or negedge rst_ni) begin : reg_chunk_idx
      if (!rst_ni) begin
        chunk_idx_q <= '0;
      end else begin
        chunk_idx_q <= chunk_idx_d;
      end
    end

    // The entropy input is forwarded to all chunks, we just control the seed enable.
    for (genvar c = 0; c < NumChunks; c++) begin : gen_seeds
      assign prng_seed[c]    = entropy_i;
      assign prng_seed_en[c] = (c == chunk_idx_q) ? entropy_req_o & entropy_ack_i : 1'b0;
    end

  end else begin : gen_packer
    // Upsizing of entropy input to correct width for reseeding the full PRNG in one shot.
    logic [Width-1:0] seed;
    logic             seed_valid;

    // Stop requesting entropy once the desired amount is available.
    assign entropy_req_o = SecSkipPRNGReseeding ? 1'b0         : reseed_req_i & ~seed_valid;
    assign reseed_ack_o  = SecSkipPRNGReseeding ? reseed_req_i : seed_valid;

    prim_packer_fifo #(
      .InW         ( EntropyWidth ),
      .OutW        ( Width        ),
      .ClearOnRead ( 1'b0         )
    ) u_prim_packer_fifo (
      .clk_i    ( clk_i         ),
      .rst_ni   ( rst_ni        ),
      .clr_i    ( 1'b0          ), // Not needed.
      .wvalid_i ( entropy_ack_i ),
      .wdata_i  ( entropy_i     ),
      .wready_o (               ), // Not needed, we're always ready to sink data at this point.
      .rvalid_o ( seed_valid    ),
      .rdata_o  ( seed          ),
      .rready_i ( 1'b1          ), // We're always ready to receive the packed output word.
      .depth_o  (               )  // Not needed.
    );

    // Extract chunk seeds. All chunks get reseeded together.
    for (genvar c = 0; c < NumChunks; c++) begin : gen_seeds
      assign prng_seed[c]    = seed[c * ChunkSize +: ChunkSize];
      assign prng_seed_en[c] = SecSkipPRNGReseeding ? 1'b0 : seed_valid;
    end
  end

  ///////////
  // LFSRs //
  ///////////

  // We use multiple LFSR instances each having a width of ChunkSize.
  for (genvar c = 0; c < NumChunks; c++) begin : gen_lfsrs
    prim_lfsr #(
      .LfsrType     ( "GAL_XOR"                                   ),
      .LfsrDw       ( ChunkSize                                   ),
      .StateOutDw   ( ChunkSize                                   ),
      .DefaultSeed  ( RndCnstLfsrSeed[c * ChunkSize +: ChunkSize] ),
      .StatePermEn  ( 1'b0                                        ),
      .NonLinearOut ( 1'b1                                        )
    ) u_lfsr_chunk (
      .clk_i     ( clk_i           ),
      .rst_ni    ( rst_ni          ),
      .seed_en_i ( prng_seed_en[c] ),
      .seed_i    ( prng_seed[c]    ),
      .lfsr_en_i ( prng_en         ),
      .entropy_i ( '0              ),
      .state_o   ( prng_state[c]   )
    );
  end

  // Add a permutation layer spanning across all LFSRs to break linear shift patterns.
  assign prng_b = prng_state;
  for (genvar b = 0; b < Width; b++) begin : gen_perm
    assign perm_b[b] = prng_b[RndCnstLfsrPerm[b]];
  end
  assign perm = perm_b;

  /////////////
  // Outputs //
  /////////////

  // To achieve independence of input and output masks (the output mask of round X is the input
  // mask of round X+1), we assign the scrambled chunks to the output data in alternating fashion.
  assign data_o = phase_q ? {perm[0], perm[NumChunks-1:1]} : perm;

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

// the code below is not meant to be synthesized,
// but it is intended to be used in simulation and FPV
`ifndef SYNTHESIS
  // Check that the supplied permutation is valid.
  logic [Width-1:0] perm_test;
  initial begin : p_perm_check
    perm_test = '0;
    for (int k = 0; k < Width; k++) begin
      perm_test[RndCnstLfsrPerm[k]] = 1'b1;
    end
    // All bit positions must be marked with 1.
    `ASSERT_I(PermutationCheck_A, &perm_test)
  end
`endif

endmodule
