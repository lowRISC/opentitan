// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * OTBN random number coordination
 *
 * This module implements the RND, RND_PREFETCH and URND CSRs/WSRs. The EDN (entropy distribution
 * network) provides the bits for random numbers. RND gives direct access to EDN bits. URND provides
 * bits from a PRNG that is seeded with bits from the EDN.
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
  parameter urnd_prng_seed_t       RndCnstUrndPrngSeed      = RndCnstUrndPrngSeedDefault
) (
  input logic clk_i,
  input logic rst_ni,

  input  logic opn_start_i,
  input  logic opn_end_i,

  input  logic            rnd_req_i,
  input  logic            rnd_prefetch_req_i,
  output logic            rnd_valid_o,
  output logic [WLEN-1:0] rnd_data_o,
  output logic            rnd_rep_err_o,
  output logic            rnd_fips_err_o,

  // Request URND PRNG reseed from the EDN
  input  logic            urnd_reseed_req_i,
  // Acknowledge URND PRNG reseed from the EDN
  output logic            urnd_reseed_ack_o,
  // When asserted PRNG state advances. It is permissible to advance the state whilst
  // reseeding.
  input  logic            urnd_advance_i,
  // URND data from PRNG
  output logic [WLEN-1:0] urnd_data_o,
  // URND lockup state detected
  output logic            urnd_all_zero_o,

  // Entropy distribution network (EDN)
  output logic                    edn_rnd_req_o,
  input  logic                    edn_rnd_ack_i,
  input  logic [EdnDataWidth-1:0] edn_rnd_data_i,
  input  logic                    edn_rnd_fips_i,
  input  logic                    edn_rnd_err_i,

  output edn_pkg::edn_req_t       edn_urnd_o,
  input  edn_pkg::edn_rsp_t       edn_urnd_i
);

  logic rnd_valid_q, rnd_valid_d;
  logic [WLEN-1:0] rnd_data_q, rnd_data_d;
  logic rnd_fips_d, rnd_fips_q;
  logic rnd_err_d, rnd_err_q;
  logic rnd_data_en;
  logic rnd_req_complete;
  logic edn_rnd_req_complete;
  logic edn_rnd_req_start;

  logic edn_rnd_req_q, edn_rnd_req_d;

  logic rnd_req_queued_d, rnd_req_queued_q;
  logic edn_rnd_data_ignore_d, edn_rnd_data_ignore_q;

  logic urnd_reseed_req_q;
  logic urnd_reseed_ack_d, urnd_reseed_ack_q;
  logic seed_en_d, seed_en_q;

  logic [WLEN-1:0] urnd_data_d, urnd_data_q;

  ////////////////////////
  // RND Implementation //
  ////////////////////////

  assign rnd_req_complete = rnd_req_i & rnd_valid_o;
  assign edn_rnd_req_complete = edn_rnd_req_o & edn_rnd_ack_i;

  assign rnd_data_en = edn_rnd_req_complete & ~edn_rnd_data_ignore_q;

  // RND becomes valid when EDN request completes and provides new bits. Valid is cleared when OTBN
  // starts a new run (opn_start_i) or when OTBN reads RND (rnd_req_complete).
  assign rnd_valid_d =
      opn_start_i || rnd_req_complete                ? 1'b0 :
      edn_rnd_req_complete && !edn_rnd_data_ignore_q ? 1'b1 : rnd_valid_q;
  assign rnd_data_d = edn_rnd_data_i;
  assign rnd_fips_d = edn_rnd_fips_i;
  assign rnd_err_d = edn_rnd_err_i;

  // Start an EDN request when there is a prefetch or an attempt at reading RND when RND data is
  // not available. Signalling `edn_rnd_req_start` whilst there is an outstanding request is
  // harmless. However, a prefetch may still be outstanding from the last OTBN run which may have
  // used a different configuration for EDN, CSRNG or the entropy source. At the start of a new
  // OTBN run, RND data is thus always invalidated and outstanding prefetches are marked such that
  // the RND data returned for the first prefetch is thrown away. When throwing away data, we need
  // to keep requesting RND data from EDN if another request got queued in the meantime.
  assign edn_rnd_req_start = (rnd_prefetch_req_i | rnd_req_i | rnd_req_queued_q) & ~rnd_valid_q;

  // When seeing a wipe with an outstanding request (which must have been a prefetch), we are going
  // to ignore the RND data that comes back from that request. Any RND data returned clears the
  // ignore status.
  assign edn_rnd_data_ignore_d =
      opn_start_i && edn_rnd_req_q ? 1'b1 :
      edn_rnd_req_complete         ? 1'b0 : edn_rnd_data_ignore_q;

  // rnd_req_queued_q shows that there's an outstanding RND prefetch whose result we are going to
  // ignore and also another request pending. Once the prefetch is done, we want to send out that
  // second request.
  //
  // The signal is set if we get a request (edn_rnd_req_start) when we're ignoring the current
  // prefetch (edn_rnd_data_ignore_q). It should be cleared when we actually start a request when
  // we're not ignoring a prefetch. It should also be cleared when finishing an operation. If that
  // happens, we were waiting to send a second prefetch and it turns out that no-one actually needed
  // the result.
  assign rnd_req_queued_d =
      opn_end_i             ? 1'b0              :
      edn_rnd_data_ignore_q ? edn_rnd_req_start :
      edn_rnd_req_start     ? 1'b0              : rnd_req_queued_q;

  // Assert `edn_rnd_req_o` when a request is started and keep it asserted until the request is
  // done.
  assign edn_rnd_req_d = (edn_rnd_req_q | edn_rnd_req_start) & ~edn_rnd_req_complete;

  assign edn_rnd_req_o = edn_rnd_req_q;

  always_ff @(posedge clk_i) begin
    if (rnd_data_en) begin
      rnd_data_q <= rnd_data_d;
      rnd_fips_q <= rnd_fips_d;
      rnd_err_q  <= rnd_err_d;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rnd_valid_q            <= 1'b0;
      rnd_req_queued_q       <= 1'b0;
      edn_rnd_req_q          <= 1'b0;
      edn_rnd_data_ignore_q  <= 1'b0;
    end else begin
      rnd_valid_q            <= rnd_valid_d;
      rnd_req_queued_q       <= rnd_req_queued_d;
      edn_rnd_req_q          <= edn_rnd_req_d;
      edn_rnd_data_ignore_q  <= edn_rnd_data_ignore_d;
    end
  end

  assign rnd_valid_o = rnd_valid_q;
  assign rnd_data_o  = rnd_data_q;

  // SEC_CM: RND.BUS.CONSISTENCY
  // SEC_CM: RND.RNG.DIGEST
  // Detect and forward RND error conditions.
  assign rnd_rep_err_o = rnd_req_complete & rnd_err_q;
  assign rnd_fips_err_o = rnd_req_complete & ~rnd_fips_q;

  /////////////////////////
  // PRNG Implementation //
  /////////////////////////

  prim_trivium #(
    .BiviumVariant(1'b1),
    .OutputWidth(WLEN),
    .StrictLockupProtection(1'b1),
    .SeedType(prim_trivium_pkg::SeedTypeStatePartial),
    .PartialSeedWidth(edn_pkg::ENDPOINT_BUS_WIDTH),
    .RndCnstTriviumLfsrSeed(RndCnstUrndPrngSeed)
  ) u_prim_trivium (
    .clk_i,
    .rst_ni,
    .en_i                (urnd_advance_i),
    .allow_lockup_i      (1'b0),
    .seed_en_i           (seed_en_q),
    .seed_done_o         (urnd_reseed_ack_d),
    .seed_req_o          (edn_urnd_o.edn_req),
    .seed_ack_i          (edn_urnd_i.edn_ack),
    .seed_key_i          ('0), // Not connected
    .seed_iv_i           ('0), // Not connected
    .seed_state_full_i   ('0), // Not connected
    .seed_state_partial_i(edn_urnd_i.edn_bus),
    .key_o               (urnd_data_d),
    .err_o               (urnd_all_zero_o)
  );

  // Buffer Bivium's output to relax timing and to prevent glitching on the URND signals.
  always_ff @(posedge clk_i) begin : proc_bivium_output_buffer
    urnd_data_q <= urnd_data_d;
  end
  assign urnd_data_o = urnd_data_q;

  // Signal urnd_reseed_req_i is high even during reset. Ensure we do not start until
  // reset has been completed
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_gate_seed_en
    if (~rst_ni) begin
      urnd_reseed_req_q <= 1'b0;
      seed_en_q         <= 1'b0;
    end else begin
      urnd_reseed_req_q <= urnd_reseed_req_i;
      seed_en_q         <= seed_en_d;
    end
  end
  assign seed_en_d = !urnd_reseed_req_q & urnd_reseed_req_i;

  // The logic around the previous PRNG (xoshiro256pp) has acknowledged the reseeding
  // operation one cycle after fetching the seed data from EDN. This cut emulates
  // this behavior.
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_delay_reseed_ack
    if (~rst_ni) begin
      urnd_reseed_ack_q <= 1'b0;
    end else begin
      urnd_reseed_ack_q <= urnd_reseed_ack_d;
    end
  end
  assign urnd_reseed_ack_o = urnd_reseed_ack_q;

  // Unused signals
  logic unused_trivium;
  assign unused_trivium = ^edn_urnd_i.edn_fips;

  `ASSERT(RndClearOnReqComplete_A, rnd_req_complete |=> ~rnd_valid_q)
  `ASSERT(UrndNoReseedOnReset_A, ~rst_ni === ~seed_en_q, clk_i, rst_ni)
endmodule
