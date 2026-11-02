// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// KMAC Entropy Generation module

`include "prim_assert.sv"

module kmac_entropy
  import kmac_pkg::*;
  import kmac_reg_pkg::*;
#(
  parameter lfsr_perm_t RndCnstLfsrPerm = RndCnstLfsrPermDefault,
  parameter lfsr_seed_t RndCnstLfsrSeed = RndCnstLfsrSeedDefault,
  parameter buffer_lfsr_seed_t RndCnstBufferLfsrSeed = RndCnstBufferLfsrSeedDefault
) (
  input clk_i,
  input rst_ni,

  // EDN interface
  output logic                            entropy_req_o,
  input                                   entropy_ack_i,
  input [edn_pkg::ENDPOINT_BUS_WIDTH-1:0] entropy_data_i,

  // Entropy to internal
  output logic                          rand_valid_o,
  output logic                          rand_early_o,
  output logic [sha3_pkg::StateW/2-1:0] rand_data_o,
  output logic                          rand_aux_o,
  input                                 rand_update_i,
  input                                 rand_consumed_i,

  // Status
  input in_keyblock_i,

  // Configurations
  input                entropy_boot_mode_i,
  input entropy_mode_e entropy_mode_i,

  //// Garbage random value when not processing Keyblock, if this config is
  //// turned on, the logic sending garbage value and never de-assert
  //// rand_valid_o unless it is not processing KeyBlock.
  input fast_process_i,

  //// PRNG enable for Message Masking
  //// If 1, PRNG advances to create 64-bit PRN. This input is used to mask
  //// the message fed into SHA3 (Keccak).
  input                       msg_mask_en_i,
  output logic [MsgWidth-1:0] msg_mask_o,

  //// SW update of seed
  input        seed_update_i,
  input [31:0] seed_data_i,

  //// SW initiated reseed requests
  input entropy_refresh_req_i,

  // Status out
  //// Hash Ops counter. Count how many hashing ops (KMAC) have run
  //// after the clear request from SW
  output logic [HashCntW-1:0] hash_cnt_o,
  input                       hash_cnt_clr_i,
  input        [HashCntW-1:0] hash_threshold_i,

  output logic entropy_ready_o,
  output logic entropy_reseeding_o,

  // Life cycle
  input  lc_ctrl_pkg::lc_tx_t lc_escalate_en_i,

  // Error output
  output logic sparse_fsm_error_o,
  output logic count_error_o
);

  /////////////////
  // Definitions //
  /////////////////

  // Encoding generated at commit ccd4447f6d using Python 3.12.13 with:
  // $ ./util/design/sparse-fsm-encode.py --language=sv \
  //     --seed 507672272 --distance 3 --states 5 --bits 6
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (50.00%)
  //  4: |||||||||||||||| (40.00%)
  //  5: |||| (10.00%)
  //  6: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 5
  // Minimum Hamming weight: 1
  // Maximum Hamming weight: 4
  //
  localparam int StateWidth = 6;

  // States
  typedef enum logic [StateWidth-1:0] {
    StRandReset = 6'b100111,
    StRandReady = 6'b110010,
    StRandEdn = 6'b111001,
    StRandSwSeedWait = 6'b000100,
    StRandTerminalError = 6'b011110
  } rand_st_e;

  /////////////
  // Signals //
  /////////////

  // PRNG primitive
  logic seed_en, seed_done;
  logic seed_req, seed_ack;
  logic [edn_pkg::ENDPOINT_BUS_WIDTH-1:0] seed;
  logic prng_en;
  logic [EntropyOutputW-1:0] prng_data, prng_data_permuted;

  // Buffer stage to prevent glitches happening inside the PRNG itself from
  // propagating into the masked processing core.
  logic [EntropyOutputW-1:0] rand_data_q;
  logic data_update;

  // Control signals for marking the PRNG output as valid towards the masked processing core.
  logic rand_valid_set, rand_valid_clear;

  // Auxiliary randomness
  logic aux_update_d, aux_update_q;
  logic aux_rand_d, aux_rand_q;

  // Randomness for controlling PRNG updates. This only matters for clock cycles
  // where the PRNG output is not actually used.
  logic [3:0] prng_en_rand_d, prng_en_rand_q;

  // Internal entropy request signals.
  logic entropy_req;
  logic entropy_req_hold_d, entropy_req_hold_q;

  //////////////
  // Datapath //
  //////////////

  // Hash Counter
  logic threshold_hit;

  logic hash_progress_d, hash_progress_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) hash_progress_q <= 1'b 0;
    else         hash_progress_q <= hash_progress_d;
  end

  assign hash_progress_d = in_keyblock_i;

  logic hash_cnt_clr;
  assign hash_cnt_clr = hash_cnt_clr_i || threshold_hit || entropy_refresh_req_i;

  logic hash_cnt_en;
  assign hash_cnt_en = hash_progress_q && !hash_progress_d;

  // SEC_CM CTR.REDUN
  // This primitive is used to place a hardened counter
  prim_count #(
    .Width(HashCntW)
  ) u_hash_count (
    .clk_i,
    .rst_ni,
    .clr_i(hash_cnt_clr),
    .set_i(1'b0),
    .set_cnt_i(HashCntW'(0)),
    .incr_en_i(hash_cnt_en),
    .decr_en_i(1'b0),
    .step_i(HashCntW'(1)),
    .commit_i(1'b1),
    .cnt_o(hash_cnt_o),
    .cnt_after_commit_o(),
    .err_o(count_error_o)
  );

  assign threshold_hit = |hash_threshold_i && (hash_threshold_i <= hash_cnt_o);

  // Reseed triggering ========================================================
  logic reseed_trigger_clr;
  logic reseed_trigger_d, reseed_trigger_q;

  // The entropy_refresh_req_i input from software and the threshold_hit signal
  // are both pulses. Latch them.
  assign reseed_trigger_d = entropy_refresh_req_i ||
      ((entropy_mode_i == EntropyModeEdn) && threshold_hit) ? 1'b1 :
      reseed_trigger_clr                                    ? 1'b0 : reseed_trigger_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      reseed_trigger_q <= 1'b0;
    end else begin
      reseed_trigger_q <= reseed_trigger_d;
    end
  end
  // Reseed triggering --------------------------------------------------------

  // PRNG primitive ===========================================================

  `ASSERT_KNOWN(EntropyModeKnown_A, entropy_mode_i)
  assign seed = (entropy_mode_i == EntropyModeSw) ? seed_data_i : entropy_data_i;

  // We employ a single unrolled Bivium stream cipher primitive to generate
  // 800 bits per clock cycle.
  prim_trivium #(
   .BiviumVariant         (1),
   .OutputWidth           (EntropyOutputW),
   .StrictLockupProtection(1),
   .SeedType              (prim_trivium_pkg::SeedTypeStatePartial),
   .PartialSeedWidth      (edn_pkg::ENDPOINT_BUS_WIDTH),
   .RndCnstTriviumLfsrSeed(RndCnstLfsrSeed)
  ) u_prim_trivium (
   .clk_i (clk_i),
   .rst_ni(rst_ni),

   .en_i                (prng_en || msg_mask_en_i),
   .allow_lockup_i      ('0), // Not used.
   .seed_en_i           (seed_en),
   .seed_done_o         (seed_done),
   .seed_req_o          (seed_req),
   .seed_ack_i          (seed_ack),
   .seed_key_i          ('0), // Not used.
   .seed_iv_i           ('0), // Not used.
   .seed_state_full_i   ('0), // Not used.
   .seed_state_partial_i(seed),

   .key_o(prng_data),
   .state_o(), // Not used.
   .err_o()
  );

  // Add a permutation layer to obfuscate the output of the PRNG primitive.
  for (genvar i = 0; i < EntropyOutputW; i++) begin : gen_perm
    assign prng_data_permuted[i] = prng_data[RndCnstLfsrPerm[i]];
  end

  // Buffer stage to prevent glitches happening inside the PRNG primitive from
  // propagating into the masked processing core.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rand_data_q <= RndCnstBufferLfsrSeed;
    end else if (data_update || msg_mask_en_i) begin
      rand_data_q <= prng_data_permuted;
    end
  end

  // Forwrad LSBs for masking the message.
  assign msg_mask_o = rand_data_q[MsgWidth-1:0];

  //  PRNG primitive ----------------------------------------------------------

  // Auxiliary randomness =====================================================

  // When aux_update_q is set, the current buffer output is used as auxiliary
  // randomness and - depending on whether keccak_round is parametrized to always
  // forward the buffer output and not use intermediate randomness - forwarded
  // to the DOM multipliers without them updating in this cycle. We don't need to
  // advance the PRNG as there is no risk of accidentally re-using the same
  // randomness twice since after the current cycle:
  // - We either load and re-mask the message/key which will use
  //   different PRNG output bits. The PRNG is advanced once per 64 bits
  //   loaded.
  // - Or, the Keccak/SHA3 core is operated but it always starts with
  //   the linear layers which don't require fresh randomness. While
  //   processing the linear layers, the PRNG is advanced to have fresh
  //   randomness for the non-linear layer requiring it.
  assign aux_rand_d = aux_update_q ? rand_data_q[EntropyOutputW - 1] :
                                     aux_rand_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      aux_update_q <= '0;
      aux_rand_q   <= '0;
    end else begin
      aux_update_q <= aux_update_d;
      aux_rand_q   <= aux_rand_d;
    end
  end

  // Auxiliary randomness -----------------------------------------------------

  // PRNG enable randomness ===================================================
  assign prng_en_rand_d =
      aux_update_q ? rand_data_q[EntropyOutputW - 2 -: 4] : // refresh
                     {1'b0, prng_en_rand_q[3:1]};           // shift out

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      prng_en_rand_q <= '0;
    end else begin
      prng_en_rand_q <= prng_en_rand_d;
    end
  end

  // PRNG enable randomness ---------------------------------------------------

  // Randomness outputs =======================================================
  assign rand_data_o = rand_data_q;
  assign rand_aux_o = aux_rand_q;

  // Signal to consumers that the currently observed randomness is valid.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rand_valid_o <= 1'b 0;
    end else if (rand_valid_set) begin
      rand_valid_o <= 1'b 1;
    end else if (rand_valid_clear) begin
      rand_valid_o <= 1'b 0;
    end
  end

  // Let consumers know that the randomness will be valid in the next clock cycle.
  assign rand_early_o = rand_valid_set;

  // The Keccak core is not supposed to ever consume randomness unless it's marked
  // as valid. The only exception is if the reseeding of the PRNG just finished
  // in the previous clock cycle. Because it's possible for the randomness to stay
  // valid throughout the reseeding (the valid is for sure de-asserted at the end).
  // The Keccak core may base its decision to start processing / consuming entropy
  // before the valid is de-asserted. If this happens, the current buffer output
  // might be used for both remasking and as auxiliary randomness which isn't ideal
  // but given this happens only very rarely it should be okay.
  `ASSUME(ConsumeNotAssertWhenNotValid_M,
      rand_update_i | rand_consumed_i |-> rand_valid_o || $past(seed_done))

  // Upon escalation the entropy_req signal can be dropped before getting
  // acknowledged. This may leave EDN in a strange state. We thus hold the request
  // until it's actually acknowledged. In case the request is acknowledged while the
  // FSM is in the StRandErr already, the incoming entropy is simply dropped.
  assign entropy_req_o      = entropy_req | entropy_req_hold_q;
  assign entropy_req_hold_d = (entropy_req_hold_q | entropy_req) & ~entropy_ack_i;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      entropy_req_hold_q <= '0;
    end else begin
      entropy_req_hold_q <= entropy_req_hold_d;
    end
  end

  // Randomness outputs -------------------------------------------------------

  ///////////////////
  // State Machine //
  ///////////////////

  rand_st_e st, st_d;

  // State FF
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, st_d, st, rand_st_e, StRandReset)

  // State: Next State and Output Logic
  // SEC_CM: FSM.SPARSE
  always_comb begin
    st_d = st;
    sparse_fsm_error_o = 1'b0;

    reseed_trigger_clr = 1'b0;

    // Signals controlling rand_valid_o and rand_early_o. The Keccak core
    // signals rand_consumed_i once per Keccak round which triggers
    // aux_update_d/q each time.
    rand_valid_set   = aux_update_q;
    rand_valid_clear = 1'b0;

    // PRNG reseed handling
    seed_en = 1'b0;
    seed_ack = 1'b0;
    entropy_req = 1'b0;

    // Randomness control signals. Randomly update the PRNG when updating the
    // auxiliary randomness but don't update the buffer stage in this case. PRNG
    // updates triggered by the Keccak core as well as the associated buffer
    // stage updates are handled below.
    prng_en = aux_update_q ? prng_en_rand_q[0] : 1'b0;
    data_update = 1'b0;
    aux_update_d = 1'b0;

    // Status
    entropy_ready_o     = aux_update_q;
    entropy_reseeding_o = 1'b0;

    unique case (st)
      StRandReset: begin
        // Reset state. The PRNG is in Entropy Boot Mode meaning the entropy is not marked as
        // ready towards the status CSR and the application interfaces. To enable ROM_CTRL
        // performing the initial ROM check, the PRNG output is marked as valid towards the
        // Keccak core.
        if (!entropy_boot_mode_i) begin
          // Software has now disabled the Entropy Boot Mode.
          rand_valid_clear = 1'b1;

          // Start reseeding the PRNG.
          seed_en = 1'b1;
          if (entropy_mode_i == EntropyModeSw) begin
            st_d = StRandSwSeedWait;
          end else begin
            st_d = StRandEdn;
          end
        end else begin
          // Until software actually disables the Entropy Boot Mode, mark the entropy as valid
          // towards the Keccak core to enable the application interface connected to ROM_CTRL
          // to forward out of reset.
          rand_valid_set = 1'b1;
        end
      end

      StRandReady: begin
        // The PRNG has been reseeded, the entropy is marked ready and the Keccak core can
        // perform masked operations.

        // Status
        entropy_ready_o = 1'b1;

        // Randomly update PRNG based on the shift register but don't update the
        // buffer stage during these random updates to prevent glitches in the
        // Keccak core.
        prng_en = prng_en_rand_q[0];

        // Deliver randomness to the Keccak core.
        if ((rand_update_i || rand_consumed_i) &&
            ((fast_process_i && in_keyblock_i) || !fast_process_i)) begin
          // Update the PRNG and the buffer stage as requested by the Keccak
          // core.
          prng_en = 1'b1;
          data_update = 1'b1;

          // Trigger an update of the auxiliary randomness.
          if (rand_consumed_i) begin
            aux_update_d = 1'b1;
            rand_valid_clear = 1'b1;
          end
        end

        // Start reseeding the PRNG.
        if (reseed_trigger_q) begin
          seed_en = 1'b1;
          if (entropy_mode_i == EntropyModeSw) begin
            st_d = StRandSwSeedWait;
          end else begin
            st_d = StRandEdn;
          end
        end
      end

      StRandEdn: begin
        // Reseed the PRNG with entropy from EDN.

        // Status
        entropy_reseeding_o = 1'b1;

        // Forward request of PRNG primitive.
        entropy_req = seed_req;

        // Randomly update PRNG based on the shift register but don't update the
        // buffer stage during these random updates to prevent glitches in the
        // Keccak core. The PRNG primitive can handle reseeding and randomness
        // requests in parallel.
        prng_en = prng_en_rand_q[0];

        // Keep delivering randomness to the Keccak core.
        if ((rand_update_i || rand_consumed_i) &&
            ((fast_process_i && in_keyblock_i) || !fast_process_i)) begin
          // Update the PRNG and the buffer stage as requested by the Keccak
          // core.
          prng_en = 1'b1;
          data_update = 1'b1;

          // Trigger an update of the auxiliary randomness.
          if (rand_consumed_i) begin
            aux_update_d = 1'b1;
            rand_valid_clear = 1'b1;
          end
        end

        // Forward EDN entropy to PRNG primitive.
        seed_ack = entropy_req_o & entropy_ack_i;

        // Finish the reseed operation. If this is the very first reseed
        // operation (rand_valid_o is still low), also trigger an update of the
        // auxiliary randomness which will set rand_valid_o. Otherwise, we let
        // the Keccak core trigger these udpates to keep the auxiliary
        // randomness and the Keccak core in sync.
        if (seed_done) begin
          reseed_trigger_clr = 1'b1;
          aux_update_d = ~rand_valid_o;
          st_d = StRandReady;
        end
      end

      StRandSwSeedWait: begin
        // Reseed the PRNG with entropy provided by software.

        // Status
        entropy_reseeding_o = 1'b1;

        // Randomly update PRNG based on the shift register but don't update the
        // buffer stage during these random updates to prevent glitches in the
        // Keccak core. The PRNG primitive can handle reseeding and randomness
        // requests in parallel.
        prng_en = prng_en_rand_q[0];

        // Keep delivering randomness to the Keccak core.
        if ((rand_update_i || rand_consumed_i) &&
            ((fast_process_i && in_keyblock_i) || !fast_process_i)) begin
          // Update the PRNG and the buffer stage as requested by the Keccak
          // core.
          prng_en = 1'b1;
          data_update = 1'b1;

          // Trigger an update of the auxiliary randomness.
          if (rand_consumed_i) begin
            aux_update_d = 1'b1;
            rand_valid_clear = 1'b1;
          end
        end

        // Forward software entropy to PRNG primitive.
        seed_ack = seed_req & seed_update_i;

        // Finish the reseed operation. If this is the very first reseed
        // operation (rand_valid_o is still low), also trigger an update of the
        // auxiliary randomness which will set rand_valid_o. Otherwise, we let
        // the Keccak core trigger these udpates to keep the auxiliary
        // randomness and the Keccak core in sync.
        if (seed_done) begin
          reseed_trigger_clr = 1'b1;
          aux_update_d = ~rand_valid_o;
          st_d = StRandReady;
        end
      end

      StRandTerminalError: begin
        // This is the terminal error state.
        sparse_fsm_error_o = 1'b1;
      end

      default: begin
        st_d = StRandTerminalError;
        sparse_fsm_error_o = 1'b1;
      end
    endcase

    // SEC_CM: FSM.GLOBAL_ESC, FSM.LOCAL_ESC
    // Unconditionally jump into the terminal error state
    // if the life cycle controller triggers an escalation.
    if (lc_ctrl_pkg::lc_tx_test_true_loose(lc_escalate_en_i)) begin
      st_d = StRandTerminalError;
    end
  end
  `ASSERT_KNOWN(RandStKnown_A, st)

  ////////////////
  // Assertions //
  ////////////////

  // The EDN bus width needs to be equal to the width of the ENTROPY_SEED
  // register as this module doesn't perform width adaption.
  `ASSERT_INIT(EdnBusWidth_A, edn_pkg::ENDPOINT_BUS_WIDTH == 32)

// the code below is not meant to be synthesized,
// but it is intended to be used in simulation and FPV
`ifndef SYNTHESIS
  // Check that the supplied permutations are valid.
  logic [EntropyOutputW-1:0] perm_test;
  initial begin : p_perm_check
    perm_test = '0;
    for (int k = 0; k < EntropyOutputW; k++) begin
      perm_test[RndCnstLfsrPerm[k]] = 1'b1;
    end
    // All bit positions must be marked with 1.
    `ASSERT_I(PermutationCheck_A, &perm_test)
  end
`endif

endmodule : kmac_entropy
