// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * OTBN random number coordination
 *
 * This module implements the RND, RND_PREFETCH and URND CSRs/WSRs. The EDN (entropy distribution
 * network) provides the bits for random numbers. RND gives direct access to EDN bits. URND provides
 * bits from an LFSR that is seeded with bits from the EDN.
 */

////////////////////////////////////////////////////////////////////////////////////////////////////
// IMPORTANT NOTE:                                                                                //
//                                   DO NOT USE THIS BLINDLY!                                     //
//                                                                                                //
// This is an initial prototype of the random number functionality in OTBN. Details are still     //
// under discussion and subject to change. It has not yet been verified this provides the         //
// necessary guarantees required for the various uses of random numbers in OTBN software.         //
////////////////////////////////////////////////////////////////////////////////////////////////////

module otbn_rnd import otbn_pkg::*;
#(
  parameter urnd_lfsr_seed_t       RndCnstUrndLfsrSeed      = RndCnstUrndLfsrSeedDefault,
  parameter urnd_chunk_lfsr_perm_t RndCnstUrndChunkLfsrPerm = RndCnstUrndChunkLfsrPermDefault
) (
  input logic clk_i,
  input logic rst_ni,

  input  logic            rnd_req_i,
  input  logic            rnd_prefetch_req_i,
  output logic            rnd_valid_o,
  output logic [WLEN-1:0] rnd_data_o,

  // Request URND LFSR reseed from the EDN
  input  logic            urnd_reseed_req_i,
  // Remains asserted whilst reseed is in progress
  output logic            urnd_reseed_busy_o,
  // When asserted URND LFSR state advances. It is permissible to advance the state whilst
  // reseeding.
  input  logic            urnd_advance_i,
  // URND data from LFSR
  output logic [WLEN-1:0] urnd_data_o,

  // Entropy distribution network (EDN)
  output logic                    edn_rnd_req_o,
  input  logic                    edn_rnd_ack_i,
  input  logic [EdnDataWidth-1:0] edn_rnd_data_i,

  output logic                    edn_urnd_req_o,
  input  logic                    edn_urnd_ack_i,
  input  logic [EdnDataWidth-1:0] edn_urnd_data_i
);
  // Determine how many LFSR chunks are required to fill a full WLEN register
  localparam int LfsrChunksPerWLEN = WLEN / UrndChunkLfsrWidth;
  localparam int BytesPerLfsrChunk = UrndChunkLfsrWidth / 8;

  logic rnd_valid_q, rnd_valid_d;
  logic [WLEN-1:0] rnd_data_q, rnd_data_d;
  logic rnd_data_en;
  logic rnd_req_complete;
  logic edn_rnd_req_complete;
  logic edn_rnd_req_start;

  logic edn_rnd_req_q, edn_rnd_req_d;

  ////////////////////////
  // RND Implementation //
  ////////////////////////

  assign rnd_req_complete = rnd_req_i & rnd_valid_o;
  assign edn_rnd_req_complete = edn_rnd_req_o & edn_rnd_ack_i;

  assign rnd_data_en = edn_rnd_req_complete;
  // RND becomes valid when EDN request completes and provides new bits. Valid is cleared when OTBN
  // reads RND
  assign rnd_valid_d = (rnd_valid_q & ~rnd_req_complete) | edn_rnd_req_complete;
  assign rnd_data_d = edn_rnd_data_i;

  // Start an EDN request when there is a prefetch or an attempt at reading RND when RND data is not
  // available. Signalling `edn_rnd_req_start` whilst there is an outstanding request has no effect
  // and is harmless.
  assign edn_rnd_req_start = rnd_prefetch_req_i | (rnd_req_i & ~rnd_valid_q);

  // Assert `edn_rnd_req_o` when a request is started and keep it asserted until the request is done
  assign edn_rnd_req_d = (edn_rnd_req_q | edn_rnd_req_start) & ~edn_rnd_req_complete;

  assign edn_rnd_req_o = edn_rnd_req_q;

  always_ff @(posedge clk_i) begin
    if (rnd_data_en) begin
      rnd_data_q <= rnd_data_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rnd_valid_q   <= 1'b0;
      edn_rnd_req_q <= 1'b0;
    end else begin
      rnd_valid_q   <= rnd_valid_d;
      edn_rnd_req_q <= edn_rnd_req_d;
    end
  end

  assign rnd_valid_o = rnd_valid_q;
  assign rnd_data_o  = rnd_data_q;

  /////////////////////////
  // URND Implementation //
  /////////////////////////

  logic edn_urnd_req_complete;
  logic edn_urnd_req_q, edn_urnd_req_d;

  assign edn_urnd_req_complete = edn_urnd_req_o & edn_urnd_ack_i;
  assign edn_urnd_req_d = (edn_urnd_req_q | urnd_reseed_req_i) & ~edn_urnd_req_complete;

  assign edn_urnd_req_o = edn_urnd_req_q;
  assign urnd_reseed_busy_o = edn_urnd_req_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      edn_urnd_req_q <= 1'b0;
    end else begin
      edn_urnd_req_q <= edn_urnd_req_d;
    end
  end

  logic lfsr_seed_en;
  logic [UrndChunkLfsrWidth-1:0] lfsr_seed  [LfsrChunksPerWLEN];
  logic [UrndChunkLfsrWidth-1:0] lfsr_state [LfsrChunksPerWLEN];

  assign lfsr_seed_en = edn_urnd_req_complete;

  // We use multiple LFSR instances each having a width of ChunkSize.
  // This is a functional prototype of the final URND functionality and is subject to change
  // https://github.com/lowRISC/opentitan/issues/6083
  for (genvar c = 0; c < LfsrChunksPerWLEN; c++) begin : gen_lfsr_chunks
    localparam logic [UrndChunkLfsrWidth-1:0] LfsrChunkSeed =
        RndCnstUrndLfsrSeed[c * UrndChunkLfsrWidth +: UrndChunkLfsrWidth];

    assign lfsr_seed[c] = edn_urnd_data_i[c * UrndChunkLfsrWidth+: UrndChunkLfsrWidth];

    prim_lfsr #(
      .LfsrType    ( "GAL_XOR"                ),
      .LfsrDw      ( UrndChunkLfsrWidth       ),
      .StateOutDw  ( UrndChunkLfsrWidth       ),
      .DefaultSeed ( LfsrChunkSeed            ),
      .StatePermEn ( 1'b1                     ),
      .StatePerm   ( RndCnstUrndChunkLfsrPerm )
    ) u_lfsr_chunk (
      .clk_i     ( clk_i          ),
      .rst_ni    ( rst_ni         ),
      .seed_en_i ( lfsr_seed_en   ),
      .seed_i    ( lfsr_seed[c]   ),
      .lfsr_en_i ( urnd_advance_i ),
      .entropy_i ( '0             ),
      .state_o   ( lfsr_state[c]  )
    );
  end

  // Further "scramble" the LFSR state at the byte level to break linear shift patterns.
  for (genvar c = 0; c < LfsrChunksPerWLEN; c++) begin : gen_lfsr_state_scramble_outer
    for (genvar b = 0;b < BytesPerLfsrChunk; b++) begin : gen_lfsr_start_scramble_inner
      assign urnd_data_o[b * 8 + c * UrndChunkLfsrWidth +: 8] =
        prim_cipher_pkg::sbox4_8bit(lfsr_state[c][b*8 +: 8], prim_cipher_pkg::PRINCE_SBOX4);
    end
  end

  `ASSERT(rnd_clear_on_req_complete, rnd_req_complete |=> ~rnd_valid_q)
endmodule
