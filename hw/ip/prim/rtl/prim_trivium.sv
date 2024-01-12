// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Trivium and Bivium stream cipher primitives
//
// This module implements the Trivium [1] and its reduced variant Bivium [2] (more precisely
// Bivium B) stream cipher primitives. Internally, they use 3 (Trivium) or 2 (Bivium) non-linear
// feedback shift registers (NFSRs). The number of output bits produced per update can flexibly
// be tuned using the OutputWidth parameter to match the needs of integrators. Up to an output
// width of 64 bits, the critical path stays unchanged. For output widths above 64 bits, the
// critical path starts to increase. The asymptotic area of the two primitives is 30 GE / output
// bit (Trivium) and 20 GE / output bit (Bivium). For a thorough analysis of the two primitives
// including security evaluation, as well as area and critical path figures, refer to [3].
//
// As thoroughly analyzed in [3], these primitives are suitable to be used as pseudo-random
// number generators for masking countermeasures in hardware.
//
// This implementation supports three different reseeding interfaces which can be selected using
// the SeedType parameter:
// 1. SeedTypeKeyIv: 2 x 80 bits for key and IV need to be provided. Before the key stream becomes
//    usable, the primitive needs to be updated 1152 / OutputWidth (Trivium) or
//    708 / OutputWidth (Bivium) times. These initial updates are performed automatically by the
//    primitives. Once the reseeding and the following initialization are done, this is indicated
//    with the seed_done_o output.
// 2. SeedTypeStateFull: The full 288-bit (Trivium) or 177-bit (Bivium) state is reseeded in one
//    shot.
// 3. SeedTypeStatePartial: PartialSeedWidth bits at a time are injected into the state. The
//    primitive latches the seed_en_i signal and keeps requesting entropy until every
//    PartialSeedWidth-wide part of the state has been overwritten once.
//    To enable updating the primitive and using the key stream during the reseed operation, the
//    number of output bits produced per update (OutputWidth) should be greater than the width of
//    the smallest NFSR in the primitve (MinNfsrWidth = 84). Thanks to the strong diffusion
//    properties of the primitives, the majority of state and key stream bits change after
//    reseeding the first state part and performing the first couple of updates if OutputWidth is
//    chosen sufficiently large. For Bivium, a quick evaluation hints that for OutputWidth equal
//    to 84, the key stream seems usable after 3 updates and most state bits seem to change after
//    5 updates. For OutputWidth equal to 160, the key stream seems usable after only 2 updates and
//    most state bits seem to change after 3 updates.
//    If the next PartialSeedWidth bits of entropy arrive after having done at least one update
//    but the new entropy hasn't sufficiently diffused yet into the state, there is a risk that
//    previously injected entropy bits are partially or completely overwritten. It is the job of
//    the integrator to ensure sufficiently many updates are performed between reseeding state
//    parts. In practice, this should be relatively simple as there is typically a minimal latency
//    between receiving entropy bits, e.g., due to clock domain crossings in the system.
//    Independently of the chosen OutputWidth parameter, it's always safe to reseed the primitive
//    while it's completely idle.
//
// For details, see the following specifications and papers:
// [1] De Canniere, "Trivium Specifications" available at
//     https://www.ecrypt.eu.org/stream/p3ciphers/trivium/trivium_p3.pdf
// [2] Raddum "Cryptanalytic Results on Trivium" available at
//     https://www.ecrypt.eu.org/stream/papersdir/2006/039.ps
// [3] Cassiers, "Randomness Generation for Secure Hardware Masking - Unrolled Trivium to the
//     Rescue" available at https://eprint.iacr.org/2023/1134

`include "prim_assert.sv"

module prim_trivium import prim_trivium_pkg::*;
#(
  parameter bit          BiviumVariant = 0,          // 0: Trivium, 1: Bivium
  parameter int unsigned OutputWidth = 64,           // Number of output bits generated per update.
  parameter bit          StrictLockupProtection = 1, // Upon entering an all zero state, 1: always
                                                     // restore to the default seed, or 0: allow
                                                     // to keep the all zero state if requested by
                                                     // allow_lockup_i.
  parameter seed_type_e  SeedType = SeedTypeStateFull, // Reseeding inteface selection, see
                                                       // prim_trivium_pkg.sv for possible values.
  parameter int unsigned PartialSeedWidth = PartialSeedWidthDefault,

  // derived parameter
  localparam int unsigned StateWidth = BiviumVariant ? BiviumStateWidth : TriviumStateWidth,

  parameter trivium_lfsr_seed_t RndCnstTriviumLfsrSeed = RndCnstTriviumLfsrSeedDefault,

  // derived parameter
  localparam logic [StateWidth-1:0] StateSeed = RndCnstTriviumLfsrSeed[StateWidth-1:0]
) (
  input logic clk_i,
  input logic rst_ni,

  input  logic                        en_i,                 // Update the primitive.
  input  logic                        allow_lockup_i,       // Allow locking up in all zero state.
                                                            // Only taken into account if
                                                            // LockupParameter = 0
  input  logic                        seed_en_i,            // Start reseeding (pulse or level).
  output logic                        seed_done_o,          // Reseeding is done (pulse).
  output logic                        seed_req_o,           // Seed REQ handshake signal
  input  logic                        seed_ack_i,           // Seed ACK handshake signal
  input  logic [KeyIvWidth-1:0]       seed_key_i,           // Seed input for SeedTypeKeyIV
  input  logic [KeyIvWidth-1:0]       seed_iv_i,            // Seed input for SeedTypeKeyIV
  input  logic [StateWidth-1:0]       seed_state_full_i,    // Seed input for SeedTypeStateFull
  input  logic [PartialSeedWidth-1:0] seed_state_partial_i, // Seed input for SeedTypeStatePartial

  output logic [OutputWidth-1:0] key_o, // Key stream output
  output logic                   err_o  // The primitive entered an all zero state and may have
                                        // locked up or entered the default state defined by
                                        // RndCnstTriviumLfsrSeed depending on the
                                        // StrictLockupProtection parameter and the allow_lockup_i
                                        // signal.
);

  localparam int unsigned LastStatePartFractional = StateWidth % PartialSeedWidth != 0 ? 1 : 0;
  localparam int unsigned NumStateParts = StateWidth / PartialSeedWidth + LastStatePartFractional;
  localparam int unsigned NumBitsLastPart = StateWidth - (NumStateParts - 1) * PartialSeedWidth;
  localparam int unsigned LastStatePart = NumStateParts - 1;
  // Width of the variable determining which state part to overwrite with the next partial seed.
  localparam int unsigned StateIdxWidth = prim_util_pkg::vbits(NumStateParts);

  logic [StateWidth-1:0] state_d, state_q;
  logic [StateWidth-1:0] state_update, state_seed;
  logic seed_req_d, seed_req_q;
  logic unused_seed;
  logic update, update_init, wr_en_seed;
  logic [StateIdxWidth-1:0] state_idx_d, state_idx_q;
  logic last_state_part;
  logic lockup, restore;

  assign update = en_i | update_init;
  assign wr_en_seed = seed_req_o & seed_ack_i;
  assign lockup = ~(|state_q);
  assign err_o = lockup;

  //////////////////////////////////////////////////
  // Regular state updating and output generation //
  //////////////////////////////////////////////////

  // The current key stream depends on the current state only.
  if (BiviumVariant) begin : gen_update_and_output_bivium
    always_comb begin
      state_update = state_q;
      for (int unsigned i = 0; i < OutputWidth; i++) begin
        key_o[i] = bivium_generate_key_stream(state_update);
        state_update = bivium_update_state(state_update);
      end
    end
  end else begin : gen_update_and_output_trivium
    always_comb begin
      state_update = state_q;
      for (int unsigned i = 0; i < OutputWidth; i++) begin
        key_o[i] = trivium_generate_key_stream(state_update);
        state_update = trivium_update_state(state_update);
      end
    end
  end

  ///////////////
  // Reseeding //
  ///////////////

  if (SeedType == SeedTypeKeyIv) begin : gen_seed_type_key_iv
    if (BiviumVariant) begin : gen_seed_type_key_iv_bivium
      assign state_seed = bivium_seed_key_iv(seed_key_i, seed_iv_i);
    end else begin : gen_seed_type_key_iv_trivium
      assign state_seed = trivium_seed_key_iv(seed_key_i, seed_iv_i);
    end

  end else if (SeedType == SeedTypeStateFull) begin : gen_seed_type_state_full
    assign state_seed = seed_state_full_i;

  end else begin : gen_seed_type_state_partial
    // If the primitive is idle and an update is not currently being requested (update = 1'b0), the
    // parts not currently being reseeded remain constant, i.e., the update function above doesn't
    // modify the state. This is required to put the primitive into a known state e.g. for known
    // answer testing.
    // If the primitive is busy and an update is requested, the update function always modifies
    // the state (but the part currently being reseeded is solely determined by the new seed).
    // Otherwise the primitive could potentially produce the same key stream output twice in a row.
    always_comb begin
      state_seed = !update ? state_q : state_update;
      // The last part may be shorter than PartialSeedWidth.
      if (last_state_part) begin
        state_seed[StateWidth - 1 -: NumBitsLastPart] = seed_state_partial_i[NumBitsLastPart-1:0];
      end else begin
        state_seed[state_idx_q * PartialSeedWidth +: PartialSeedWidth] = seed_state_partial_i;
      end
    end
  end

  /////////////////////////////////
  // State register and updating //
  /////////////////////////////////

  // The lockup protection can optionally be disabled at run time. This may be required to put the
  // primitive into an all zero state, e.g., to switch off masking countermeasures for analysis if
  // the primitive is used for generating masks. However, the err_o bit always signals this
  // condition to the outside.
  assign restore = lockup & (StrictLockupProtection | ~allow_lockup_i);
  assign state_d = restore     ? StateSeed    :
                   wr_en_seed  ? state_seed   :
                   update      ? state_update : state_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : state_reg
    if (!rst_ni) begin
      state_q <= StateSeed;
    end else begin
      state_q <= state_d;
    end
  end

  // Latch the seed enable signal and keep the request high until the last request is acknowledged.
  assign seed_req_d = (seed_en_i | seed_req_q) & (~seed_ack_i | ~last_state_part);
  always_ff @(posedge clk_i or negedge rst_ni) begin : seed_req_reg
    if (!rst_ni) begin
      seed_req_q <= 1'b0;
    end else begin
      seed_req_q <= seed_req_d;
    end
  end
  assign seed_req_o = seed_en_i | seed_req_q;

  if (SeedType == SeedTypeKeyIv) begin : gen_key_iv_seed_handling
    // After receiving key and IV, the entire state needs to be updated 4 times before the key
    // stream becomes usable. Depending on OutputWidth, a different number of initial updates are
    // required for this. [3]
    localparam int unsigned NumInitUpdatesFractional = (StateWidth * 4) % OutputWidth != 0 ? 1 : 0;
    localparam int unsigned NumInitUpdates =
        (StateWidth * 4) / OutputWidth + NumInitUpdatesFractional;
    localparam int unsigned LastInitUpdate = NumInitUpdates - 1;
    localparam int unsigned InitUpdatesCtrWidth = prim_util_pkg::vbits(NumInitUpdates);

    logic [InitUpdatesCtrWidth-1:0] init_update_ctr_d, init_update_ctr_q;
    logic init_update_d, init_update_q;
    logic last_init_update;

    // Count the number of initial updates done.
    assign init_update_ctr_d = wr_en_seed    ? '0                       :
                               init_update_q ? init_update_ctr_q + 1'b1 : init_update_ctr_q;
    always_ff @(posedge clk_i or negedge rst_ni) begin : init_update_ctr_reg
      if (!rst_ni) begin
        init_update_ctr_q <= '0;
      end else begin
        init_update_ctr_q <= init_update_ctr_d;
      end
    end

    // Track whether we're currently doing the initial updates.
    assign last_init_update = init_update_ctr_q == LastInitUpdate[InitUpdatesCtrWidth-1:0];
    assign init_update_d = wr_en_seed       ? 1'b1 :
                           last_init_update ? 1'b0 : init_update_q;
    always_ff @(posedge clk_i or negedge rst_ni) begin : init_update_reg
      if (!rst_ni) begin
        init_update_q <= 1'b0;
      end else begin
        init_update_q <= init_update_d;
      end
    end
    assign update_init = init_update_q;

    // We're done after performing the initial updates.
    assign seed_done_o = init_update_q & last_init_update;

    // Tie off unused signals.
    assign state_idx_d = '0;
    assign state_idx_q = '0;
    assign last_state_part = 1'b0;
    assign unused_seed = ^{seed_state_full_i,
                           seed_state_partial_i,
                           state_idx_d,
                           state_idx_q,
                           last_state_part};

  end else if (SeedType == SeedTypeStateFull) begin : gen_full_seed_handling

    // Only one handshake is required.
    assign seed_done_o = seed_req_o & seed_ack_i;

    // Tie off unused signals.
    assign update_init = 1'b0;
    assign state_idx_d = '0;
    assign state_idx_q = '0;
    assign last_state_part = 1'b1;
    assign unused_seed = ^{seed_key_i,
                           seed_iv_i,
                           seed_state_partial_i,
                           state_idx_d,
                           state_idx_q,
                           last_state_part};

  end else begin : gen_partial_seed_handling

    // Seed PartialSeedWidth bits of the state at a time. Track the part idx using a counter. The
    // counter is reset when seeding the last part.
    assign last_state_part = state_idx_q == LastStatePart[StateIdxWidth-1:0];
    assign state_idx_d = wr_en_seed &  last_state_part ? '0                 :
                         wr_en_seed & ~last_state_part ? state_idx_q + 1'b1 : state_idx_q;
    always_ff @(posedge clk_i or negedge rst_ni) begin : state_idx_reg
      if (!rst_ni) begin
        state_idx_q <= '0;
      end else begin
        state_idx_q <= state_idx_d;
      end
    end

    // We're done upon receiving the last state part.
    assign seed_done_o = seed_req_o & seed_ack_i & last_state_part;

    // Tie off unused signals.
    assign update_init = 1'b0;
    assign unused_seed = ^{seed_key_i,
                           seed_iv_i,
                           seed_state_full_i};
  end

  /////////////////
  // Asssertions //
  /////////////////

  // While performing a partial reseed of the state, the primitive can be updated. However, this
  // should only be done if the number of produced bits per update / shift amount per update is
  // greater than the width of the smallest NFSR (= 84) inside the primitve. Otherwise, there is a
  // risk of overwriting the previously provided partial seed which reduces the amount of fresh
  // entropy injected per full reseed operation.
  `ASSERT(PrimTriviumPartialStateSeedWhileUpdate_A,
      (SeedType == SeedTypeStatePartial) && seed_req_o && en_i |-> OutputWidth >= MinNfsrWidth)

endmodule
