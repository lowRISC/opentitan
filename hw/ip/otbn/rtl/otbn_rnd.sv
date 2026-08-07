// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * OTBN random number coordination
 *
 * This module implements the RND, RND_PREFETCH and URND CSRs/WSRs. The EDN (entropy distribution
 * network) provides the bits for random numbers. RND gives direct access to EDN bits. URND
 * provides bits from a PRNG that is seeded with bits from the EDN. The PRNG can be stopped and
 * resumed by SW at runtime via the URND control interface. This interface also allows to save and
 * restore a PRNG state.
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
  input  logic urnd_reseed_req_i,
  // Acknowledge URND PRNG reseed from the EDN
  output logic urnd_reseed_ack_o,

  input  logic urnd_ctrl_enabled_i,
  // When asserted, PRNG state advances except it is stopped by SW. It is permissible to advance
  // the state whilst reseeding.
  input  logic urnd_advance_i,
  // When asserted, PRNG state advances independently of what SW commanded via URND CTRL.
  input  logic urnd_must_advance_i,

  // CSRs for URND control
  input  logic        ispr_urnd_ctrl_wr_i,
  input  logic [31:0] ispr_urnd_ctrl_wdata_i,
  output logic [31:0] ispr_urnd_status_rdata_o,

  // WSR for URND control
  // The state is exposed as a WLEN vector to keep the rest of OTBN PRNG agnostic.
  // The read state is zero padded to WLEN. When writing during a restore only the lowest
  // PartialSeedWidth bits are considered.
  output logic [WLEN-1:0]    ispr_urnd_state_rdata_o,
  input  logic               ispr_urnd_state_wr_i,
  input  logic [ExtWLEN-1:0] ispr_urnd_state_wdata_i,

  // URND data from PRNG
  output logic [UrndLen-1:0] urnd_data_o,
  // URND lockup state detected
  output logic               urnd_all_zero_o,

  // Entropy distribution network (EDN)
  output logic                    edn_rnd_req_o,
  input  logic                    edn_rnd_ack_i,
  input  logic [EdnDataWidth-1:0] edn_rnd_data_i,
  input  logic                    edn_rnd_fips_i,
  input  logic                    edn_rnd_err_i,

  output edn_pkg::edn_req_t       edn_urnd_o,
  input  edn_pkg::edn_rsp_t       edn_urnd_i,

  output logic intg_err_o
);
  localparam int unsigned StateWidth = prim_trivium_pkg::BiviumStateWidth;
  localparam int unsigned PartialSeedWidth = edn_pkg::ENDPOINT_BUS_WIDTH;
  // The number of base words required to represent a partial seed. Rounds up to full base words.
  localparam int unsigned BaseWordsPerUrndSeed = (PartialSeedWidth + 31) / 32;


  typedef logic [5:0] urnd_restore_info_width_t;
  typedef logic [9:0] urnd_state_info_width_t;

  typedef struct packed {
    urnd_restore_info_width_t urnd_restore_width;
    urnd_state_info_width_t   urnd_state_width;
    logic [11:0]              rsvd;
    logic                     used_while_stopped;
    logic                     restoring;
    logic                     stopped;
    logic                     urnd_ctrl_enabled;
  } ispr_urnd_status_t;

  typedef struct packed {
    logic [31-3:0] rsvd;
    logic restore;
    logic start;
    logic stop;
  } ispr_urnd_ctrl_t;

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

  logic urnd_reseed_req_d, urnd_reseed_req_q;
  logic urnd_reseed_ack_d, urnd_reseed_ack_q;
  logic start_reseeding_d, start_reseeding_q;

  logic [UrndLen-1:0] urnd_data_d, urnd_data_q;

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

  //////////////////
  // URND control //
  //////////////////
  // This part implements the CSRs and control logic to start and stop the PRNG. It also implements
  // the logic triggering a restore process. See the PRNG implementation section for how a restore
  // is implemented.
  logic urnd_ctrl_wr, stop_cmd, start_cmd, restore_cmd;
  logic urnd_stopped_d, urnd_stopped_q;
  logic urnd_advance;
  logic used_while_stopped, used_while_stopped_d, used_while_stopped_q;
  logic start_restoring;
  logic restoring_d, restoring_q;
  logic seed_from_edn_d, seed_from_edn_q;
  logic seed_req, seed_ack;
  logic sw_seed_ack;
  logic seed_done;

  ispr_urnd_status_t ispr_urnd_status_r;
  assign ispr_urnd_status_rdata_o = ispr_urnd_status_r;

  assign ispr_urnd_status_r = '{
    urnd_restore_width: urnd_restore_info_width_t'(PartialSeedWidth),
    urnd_state_width:   urnd_state_info_width_t'(StateWidth),
    rsvd:               '0,
    used_while_stopped: used_while_stopped_q,
    restoring:          restoring_q,
    stopped:            urnd_stopped_q,
    urnd_ctrl_enabled:  urnd_ctrl_enabled_i
  };

  ispr_urnd_ctrl_t ispr_urnd_ctrl_w;
  assign ispr_urnd_ctrl_w = ispr_urnd_ctrl_wdata_i;

  // A command is only effective if the interface is enabled.
  assign urnd_ctrl_wr = ispr_urnd_ctrl_wr_i & urnd_ctrl_enabled_i;
  assign stop_cmd     = urnd_ctrl_wr & ispr_urnd_ctrl_w.stop;
  assign start_cmd    = urnd_ctrl_wr & ispr_urnd_ctrl_w.start;
  assign restore_cmd  = urnd_ctrl_wr & ispr_urnd_ctrl_w.restore;

  // Each execution starts with a running PRNG. Start has higher prio than stop. If this changes
  // the used while stopped logic probably need to be adapted as well, see below.
  assign urnd_stopped_d = opn_start_i ? 1'b0 :
                          start_cmd   ? 1'b0 :
                          stop_cmd    ? 1'b1 : urnd_stopped_q;

  // The main advance / state update control signal. Based on current instruction because the URND
  // output is registered. Otherwise we would still perform two updates.
  assign urnd_advance = urnd_must_advance_i || (urnd_advance_i && !urnd_stopped_d);

  // Detect a forced advance whilst stopped. Some must advance sources trigger one cycle before
  // URND is used such that the registered URND is advanced in time. However, if we start now, then
  // this early "must advance" signal can be ignored.
  // ATTENTION: This logic relies on the fact that a START command has higher priority than STOP.
  assign used_while_stopped = urnd_must_advance_i && urnd_stopped_q && !start_cmd;

  // A stop does only clear previous errors. But if the next insn after stop reads it, then we must
  // still set the flag.

  // We keep track of usages whilst stopped with a sticky flag. The flag is cleared once a new
  // OTBN execution starts or the PRNG is stopped. However, because instructions reading URND
  // enforce an advance one cycle before they execute, the flag must be set if:
  // The PRNG is running, a stop command is issued, and the next instruction will read URND.
  assign used_while_stopped_d = opn_start_i                                 ? 1'b0 :
                                used_while_stopped                          ? 1'b1 :
                                !urnd_stopped_q && stop_cmd && urnd_advance ? 1'b1 :
                                stop_cmd                                    ? 1'b0 :
                                                                              used_while_stopped_q;

  // Signal the start of a restoring process only if no reseed is ongoing.
  assign start_restoring = restore_cmd & ~restoring_q & ~seed_from_edn_q;

  // Keep track if a restore process is ongoing. If a restore process is taken over by a reseed
  // process we clear the flag once the reseed has ended (see below).
  assign restoring_d   = opn_start_i     ? 1'b0       :
                         restoring_q     ? ~seed_done :
                         start_restoring ? 1'b1       : restoring_q;

  // During a restore each write to URND_STATE supplies one seed word and acts as an ack for a seed
  // request.
  assign sw_seed_ack = ispr_urnd_state_wr_i & restoring_q & seed_req;

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_urnd_ctrl
    if (~rst_ni) begin
      used_while_stopped_q <= 1'b0;
      urnd_stopped_q       <= 1'b0;
      restoring_q          <= 1'b0;
    end else begin
      used_while_stopped_q <= used_while_stopped_d;
      urnd_stopped_q       <= urnd_stopped_d;
      restoring_q          <= restoring_d;
    end
  end

  /////////////////////////
  // PRNG Implementation //
  /////////////////////////
  // There are two processes which make use of the PRNG reseed interface. There is a reseed process
  // issued by the OTBN start stop controller which reseeds the PRNG with values from EDN. And
  // there is a restore process issued by OTBN SW to restore a URND context. Any reseed process has
  // priority over a restore process. Both processes share the actual reseed interface which
  // accepts partial seed values over multiple cycles. If a reseed process is issued whilst a
  // restore is ongoing, the reseeding continues the restoring process but then provides seeds from
  // EDN. All already provided seed parts are kept. As a consequence, in the worst case only the
  // final reseed word comes from EDN. However, this is ok due to the relatively large Bivium state
  // size.
  logic [BaseWordsPerUrndSeed*32-1:0] restore_seed_words_no_intg;
  logic [PartialSeedWidth-1:0] restore_seed, partial_seed;
  logic [StateWidth-1:0] current_state;

  prim_trivium #(
    .BiviumVariant(1'b1),
    .OutputWidth(UrndLen),
    .StrictLockupProtection(1'b1),
    .SeedType(prim_trivium_pkg::SeedTypeStatePartial),
    .PartialSeedWidth(edn_pkg::ENDPOINT_BUS_WIDTH),
    .RndCnstTriviumLfsrSeed(RndCnstUrndPrngSeed)
  ) u_prim_trivium (
    .clk_i,
    .rst_ni,
    .en_i                (urnd_advance),
    .allow_lockup_i      (1'b0),
    .seed_en_i           (start_reseeding_q | start_restoring),
    .seed_done_o         (seed_done),
    .seed_req_o          (seed_req),
    .seed_ack_i          (seed_ack),
    .seed_key_i          ('0), // Not connected
    .seed_iv_i           ('0), // Not connected
    .seed_state_full_i   ('0), // Not connected
    .seed_state_partial_i(partial_seed),
    .key_o               (urnd_data_d),
    .state_o             (current_state),
    .err_o               (urnd_all_zero_o)
  );

  // Signal urnd_reseed_req_i is high even during reset. Ensure we do not start until
  // reset has been completed by registering it with a resettable flop.
  assign urnd_reseed_req_d = urnd_reseed_req_i;
  assign start_reseeding_d = !urnd_reseed_req_q & urnd_reseed_req_i;

  // Keep track if the current seeding is a reseed or restore process.
  assign seed_from_edn_d = start_reseeding_d ? 1'b1 :
                           seed_done         ? 1'b0 : seed_from_edn_q;

  // Mux the seed value request depending on the type of seed process.
  assign partial_seed       = seed_from_edn_q ? edn_urnd_i.edn_bus : restore_seed;
  assign seed_ack           = seed_from_edn_q ? edn_urnd_i.edn_ack : sw_seed_ack;
  assign edn_urnd_o.edn_req = seed_from_edn_q ? seed_req : 1'b0;

  // SW writes 256 bits but we take only the relevant bits. The Bivium instance already handles the
  // case when the last seed part is narrower than the seed interface.
  assign restore_seed = restore_seed_words_no_intg[PartialSeedWidth-1:0];

  // Only a reseed acknowledges the reseed request from the start/stop controller. Otherwise a
  // restore would be flagged as spurious reseed ack.
  assign urnd_reseed_ack_d = seed_done & seed_from_edn_q;

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

  // Expose the current PRNG state, zero padded to WLEN. The WSR read path muxing must ensure that
  // the state is properly blanked and hidden when the interface is disabled (which is easily done
  // due to the onehot ISPR mux architecture). The state directly originates from flops, so no need
  // to register it again.
  assign ispr_urnd_state_rdata_o = {{{WLEN - StateWidth}{1'b0}}, current_state};

  // Buffer Bivium's output to relax timing and to prevent glitching on the URND signals.
  always_ff @(posedge clk_i) begin : proc_bivium_output_buffer
    urnd_data_q <= urnd_data_d;
  end
  assign urnd_data_o = urnd_data_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_seed_ctrl
    if (~rst_ni) begin
      urnd_reseed_req_q <= 1'b0;
      start_reseeding_q <= 1'b0;
      seed_from_edn_q   <= 1'b0;
    end else begin
      urnd_reseed_req_q <= urnd_reseed_req_d;
      start_reseeding_q <= start_reseeding_d;
      seed_from_edn_q   <= seed_from_edn_d;
    end
  end

  // Check the integrity of the provided restore state when the PRNG consumes it. We check only the
  // relevant bits. Depending on the seed width this spans over multiple base words.
  logic [1:0] urnd_state_wdata_intg_err_raw;
  for (genvar i = 0; i < BaseWordsPerUrndSeed; i++) begin : g_check_restore_seed_intg
    prim_secded_inv_39_32_dec u_rd_data_a_intg_dec (
      .data_i    (ispr_urnd_state_wdata_i[i * BaseIntgWidth +: BaseIntgWidth]),
      .data_o    (restore_seed_words_no_intg[i * 32 +: 32]),
      .syndrome_o(),
      .err_o     (urnd_state_wdata_intg_err_raw)
    );
  end

  assign intg_err_o = |urnd_state_wdata_intg_err_raw && sw_seed_ack;

  // Unused signals
  logic unused_signals;
  assign unused_signals =
      ^{edn_urnd_i.edn_fips,
        ispr_urnd_ctrl_w.rsvd,
        ispr_urnd_state_wdata_i[ExtWLEN - 1:BaseWordsPerUrndSeed * BaseIntgWidth]};

  `ASSERT(RndClearOnReqComplete_A, rnd_req_complete |=> ~rnd_valid_q)
  `ASSERT(UrndNoReseedOnReset_A, ~rst_ni === ~start_reseeding_q, clk_i, rst_ni)
endmodule
