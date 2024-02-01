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
  input entropy_mode_e mode_i,
  //// SW sets ready bit when EDN is ready to accept requests through its app.
  //// interface.
  input entropy_ready_i,

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

  //// SW may initiate manual EDN seed refresh
  input entropy_refresh_req_i,

  //// Timer limit value
  //// If value is 0, timer is disabled
  input [TimerPrescalerW-1:0] wait_timer_prescaler_i,
  input [EdnWaitTimerW-1:0]   wait_timer_limit_i,

  // Status out
  //// Hash Ops counter. Count how many hashing ops (KMAC) have run
  //// after the clear request from SW
  output logic [HashCntW-1:0] hash_cnt_o,
  input                       hash_cnt_clr_i,
  input        [HashCntW-1:0] hash_threshold_i,

  output prim_mubi_pkg::mubi4_t entropy_configured_o,

  // Life cycle
  input  lc_ctrl_pkg::lc_tx_t lc_escalate_en_i,

  // Error output
  output err_t err_o,
  output logic sparse_fsm_error_o,
  output logic count_error_o,
  input        err_processed_i
);

  /////////////////
  // Definitions //
  /////////////////

  // Timer Widths are defined in kmac_pkg

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 9 -n 10 \
  //      -s 507672272 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: ||||||||||| (13.89%)
  //  4: ||||||||||||||| (19.44%)
  //  5: |||||||||||||||||||| (25.00%)
  //  6: ||||||||||||||| (19.44%)
  //  7: ||||||||||| (13.89%)
  //  8: |||| (5.56%)
  //  9: || (2.78%)
  // 10: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 9
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 7
  //
  localparam int StateWidth = 10;

  // States
  typedef enum logic [StateWidth-1:0] {
    // Reset: Reset state. The entropy is not ready. The state machine should
    // get new entropy from EDN or the seed should be feeded by the software.
    StRandReset = 10'b1001111000,

    // The seed is fed into PRNG and the entropy is ready. It means the
    // rand_valid is asserted with valid data. It takes a few steps to reach
    // this state from StRandReset.
    StRandReady = 10'b0110000100,

    // EDN interface: Send request and receive
    // RandEdnReq state can be transit from StRandReset or from StRandReady
    //
    // Reset --> EdnReq:
    //     If entropy source module is ready, the software sets a bit in CFG
    //     also sets the entropy mode to EdnMode. Then this FSM moves to EdnReq
    //     to initialize PRNG seed.
    //
    // Ready --> EdnReq:
    //     1. If a mode is configured as to update entropy everytime it is
    //        consumed, then the FSM moves from Ready to EdnReq to refresh seed
    //     2. If the software enabled EDN timer and the timer is expired and
    //        also the KMAC is processing the key block, the FSM moves to
    //        EdnReq to refresh seed
    //     3. If a KMAC operation is completed, the FSM also refreshes the PRNG
    //        seed to prepare next KMAC op or wipe out operation.
    StRandEdn = 10'b1100100111,

    // Sw Seed: If mode is set to manual mode, This entropy module needs initial
    // seed from the software. It waits the seed update signal to expand initial
    // entropy
    StSwSeedWait = 10'b1011110110,

    // Generate: In this state, the entropy generator advances the PRNG to
    // generate the 800-bits of pseudo random data for the next evaluation.
    StRandGenerate = 10'b0000001100,

    // ErrWaitExpired: If Edn timer expires, FSM moves to this state and wait
    // the software response. Software should switch to manual mode then disable
    // the timer (to 0) and update the seed via register interface.
    StRandErrWaitExpired = 10'b0001100011,

    // ErrNoValidMode: If SW sets entropy ready but the mode is not either
    // Manual Mode nor EdnMode, this logic reports to SW with
    // NoValidEntropyMode.
    StRandErrIncorrectMode = 10'b1110010000,

    // Err: After the error is reported, FSM sits in Err state ignoring all the
    // requests. It does not generate new entropy and drops the entropy valid
    // signal.
    //
    // SW sets err_processed signal to clear the error. The software should
    // clear the entropy ready signal before clear the error interrupt so that
    // the FSM sits in StRandReset state not moving forward with incorrect
    // configurations.
    StRandErr = 10'b1000011110,

    StTerminalError = 10'b0010011000
  } rand_st_e;

  /////////////
  // Signals //
  /////////////

  // Timers
  // "Wait Timer": This timer is in active when FSM sends entropy request to EDN
  //   If EDN does not return the entropy data until the timer expired, FSM
  //   moves to error state and report the error to the system.

  localparam int unsigned TimerW = EdnWaitTimerW;
  logic timer_enable, timer_update, timer_expired, timer_pulse;
  logic [TimerW-1:0] timer_limit;
  logic [TimerW-1:0] timer_value;

  localparam int unsigned PrescalerW = TimerPrescalerW;
  logic [PrescalerW-1:0] prescaler_cnt;

  // PRNG primitive
  // SW configures to use EDN or ENTROPY_SEED register as PRNG seed
  logic seed_en, seed_done;
  logic seed_req, seed_ack;
  logic [edn_pkg::ENDPOINT_BUS_WIDTH-1:0] seed;
  logic prng_en;
  logic [EntropyOutputW-1:0] prng_data, prng_data_permuted;

  // Buffer stage to prevent glitches happening inside the PRNG itself from
  // propagating into the masked processing core.
  logic [EntropyOutputW-1:0] rand_data_q;
  logic data_update;

  // Auxliliary randomness
  logic aux_rand_d, aux_rand_q;
  logic aux_update;

  // Randomness for controlling PRNG updates. This only matters for clock cycles
  // where the PRNG output is not actually used.
  logic [3:0] prng_en_rand_d, prng_en_rand_q;

  // Entropy valid signal
  // FSM set and clear the valid signal, rand_consume signal clear the valid
  // signal. Split the set, clear to make entropy valid while FSM is processing
  // other tasks.
  logic rand_valid_set, rand_valid_clear;

  // FSM latches the mode and stores into mode_q when the FSM is out from
  // StReset. The following states, or internal datapath uses mode_q after that.
  // If the SW wants to change the mode, it requires resetting the IP.
  logic mode_latch;
  entropy_mode_e mode_q;

  // Status out: entropy configured
  prim_mubi_pkg::mubi4_t entropy_configured;

  // Internal entropy request signals.
  logic entropy_req;
  logic entropy_req_hold_d, entropy_req_hold_q;

  //////////////
  // Datapath //
  //////////////

  // For latching (`wait_timer_limit_i` != 0) during last `timer_update`
  // See #16716
  logic non_zero_wait_timer_limit;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      non_zero_wait_timer_limit <= '0;
    end else if (timer_update) begin
      non_zero_wait_timer_limit <= |wait_timer_limit_i;
    end
  end

  logic [TimerPrescalerW-1:0] wait_timer_prescaler_d;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      wait_timer_prescaler_d <= '0;
    end else if (timer_update) begin
      wait_timer_prescaler_d <= wait_timer_prescaler_i;
    end
  end

  // Timers ===================================================================
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      timer_value <= '0;
    end else if (timer_update) begin
      timer_value <= timer_limit;
    end else if (timer_expired) begin
      timer_value <= '0; // keep the value
    end else if (timer_enable && timer_pulse && |timer_value) begin // if non-zero timer v
      timer_value <= timer_value - 1'b 1;
    end
  end

  assign timer_limit = TimerW'(wait_timer_limit_i);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      timer_expired <= 1'b 0;
    end else if (timer_update) begin
      timer_expired <= 1'b 0;
    end else if (timer_enable && (timer_value == '0)) begin
      timer_expired <= 1'b 1;
    end
  end

  // Prescaler
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      prescaler_cnt <= '0;
    end else if (timer_update) begin
      prescaler_cnt <= wait_timer_prescaler_i;
    end else if (timer_enable && prescaler_cnt == '0) begin
      prescaler_cnt <= wait_timer_prescaler_d;
    end else if (timer_enable) begin
      prescaler_cnt <= prescaler_cnt - 1'b 1;
    end
  end

  assign timer_pulse = (timer_enable && prescaler_cnt == '0);
  // Timers -------------------------------------------------------------------

  // Hash Counter
  logic threshold_hit;
  logic threshold_hit_q, threshold_hit_clr; // latched hit

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

  logic hash_count_error;

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
    .err_o(hash_count_error)
  );

  assign threshold_hit = |hash_threshold_i && (hash_threshold_i <= hash_cnt_o);

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)                threshold_hit_q <= 1'b 0;
    else if (threshold_hit_clr) threshold_hit_q <= 1'b 0;
    else if (threshold_hit)     threshold_hit_q <= 1'b 1;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)         mode_q <= EntropyModeNone;
    else if (mode_latch) mode_q <= mode_i;
  end

  // PRNG primitive ===========================================================

  `ASSERT_KNOWN(ModeKnown_A, mode_i)
  assign seed = (mode_q == EntropyModeSw) ? seed_data_i : entropy_data_i;

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
  assign aux_rand_d = aux_update ? rand_data_q[EntropyOutputW - 1] :
                                   aux_rand_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      aux_rand_q <= '0;
    end else begin
      aux_rand_q <= aux_rand_d;
    end
  end

  // Auxiliary randomness -----------------------------------------------------

  // PRNG enable randomness ===================================================
  assign prng_en_rand_d =
      aux_update ? rand_data_q[EntropyOutputW - 2 -: 4] : // refresh
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

  // entropy valid
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

  // Upon escalation or in case the EDN wait timer expires the entropy_req signal
  // can be dropped before getting acknowledged. This may leave EDN in a strange
  // state. We thus hold the request until it's actually acknowledged. In case the
  // request is acknowledged while the FSM is in the StRandErr already, the
  // incoming entropy is simply dropped.
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

  // Remaining outputs
  assign count_error_o = hash_count_error;

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
    sparse_fsm_error_o = 1'b 0;

    // Default Timer values
    timer_enable = 1'b 0;
    timer_update = 1'b 0;

    threshold_hit_clr = 1'b 0;

    // rand is valid when this logic expands the entropy.
    // FSM sets the valid signal, the signal is cleared by `consume` signal
    // or FSM clear signal.
    // Why split the signal to set and clear?
    // FSM only set the signal to make entropy valid while processing other
    // tasks such as EDN request.
    rand_valid_set   = 1'b 0;
    rand_valid_clear = 1'b 0;

    // mode_latch to store mode_i into mode_q
    mode_latch = 1'b 0;

    // PRNG reseed handling
    seed_en = 1'b 0;
    seed_ack = 1'b 0;
    entropy_req = 1'b 0;

    // Randomness control signals
    prng_en = 1'b 0;
    data_update = 1'b 0;
    aux_update = 1'b 0;

    // Error
    err_o = '{valid: 1'b 0, code: ErrNone, info: '0};

    unique case (st)
      StRandReset: begin
        if (entropy_ready_i) begin

          // As SW ready, discard current dummy entropy and refresh.
          rand_valid_clear = 1'b 1;

          mode_latch = 1'b 1;
          // SW has configured KMAC
          unique case (mode_i)
            EntropyModeSw: begin
              // Start reseeding the PRNG via ENTROPY_SEED CSR.
              seed_en = 1'b 1;
              st_d = StSwSeedWait;
            end

            EntropyModeEdn: begin
              // Start reseeding the PRNG via EDN.
              seed_en = 1'b 1;
              st_d = StRandEdn;

              // Timer reset
              timer_update = 1'b 1;
            end

            default: begin
              // EntropyModeNone or other values
              // Error. No valid mode given, report to SW
              st_d = StRandErrIncorrectMode;
            end
          endcase
        end else begin
          st_d = StRandReset;

          // Setting the dummy rand gate until SW prepares.
          // This lets the Application Interface move forward out of reset
          // without SW intervention.
          rand_valid_set = 1'b 1;
        end
      end

      StRandReady: begin
        timer_enable = 1'b 1; // If limit is zero, timer won't work

        prng_en = prng_en_rand_q[0];

        if ((rand_update_i || rand_consumed_i) &&
            ((fast_process_i && in_keyblock_i) || !fast_process_i)) begin
          // If fast_process is set, don't clear the rand valid, even
          // consumed. So, the logic does not expand the entropy again.
          // If fast_process is not set, then every rand_consume signal
          // triggers rand expansion.
          prng_en = 1'b 1;
          data_update = 1'b 1;

          if (rand_consumed_i) begin
            st_d = StRandGenerate;

            rand_valid_clear = 1'b 1;
          end else begin
            st_d = StRandReady;
          end
        end else if ((mode_q == EntropyModeEdn) &&
            (entropy_refresh_req_i || threshold_hit_q)) begin
          // Start reseeding the PRNG via EDN.
          seed_en = 1'b 1;
          st_d = StRandEdn;

          // Timer reset
          timer_update = 1'b 1;

          // Clear the threshold as it refreshes the hash
          threshold_hit_clr = 1'b 1;
        end else begin
          st_d = StRandReady;
        end
      end

      StRandEdn: begin
        // Forward request of PRNG primitive.
        entropy_req = seed_req;

        // Wait timer
        timer_enable = 1'b 1;

        if (timer_expired && non_zero_wait_timer_limit) begin
          // If timer count is non-zero and expired;
          st_d = StRandErrWaitExpired;

        end else if (entropy_req_o && entropy_ack_i) begin
          seed_ack = 1'b 1;

          if (seed_done) begin
            st_d = StRandGenerate;

            if ((fast_process_i && in_keyblock_i) || !fast_process_i) begin
              prng_en = 1'b 1;
              data_update = 1'b 1;
              rand_valid_clear = 1'b 1;
            end
          end else begin
            st_d = StRandEdn;
          end
        end else if ((rand_update_i || rand_consumed_i) &&
            ((fast_process_i && in_keyblock_i) || !fast_process_i)) begin
          // Somehow, while waiting the EDN entropy, the KMAC or SHA3 logic
          // consumed the remained entropy. This can happen when the previous
          // SHA3/ KMAC op completed and this Entropy FSM has moved to this
          // state to refresh the entropy and the SW initiates another hash
          // operation while waiting for the EDN response.
          st_d = StRandEdn;

          prng_en = 1'b 1;
          data_update = 1'b 1;
          rand_valid_clear = rand_consumed_i;
        end else begin
          st_d = StRandEdn;
        end
      end

      StSwSeedWait: begin
        // Forward ack driven by software.
        seed_ack = seed_req & seed_update_i;

        if (seed_done) begin
          st_d = StRandGenerate;

          prng_en = 1'b 1;
          data_update = 1'b 1;

          rand_valid_clear = 1'b 1;
        end else begin
          st_d = StSwSeedWait;
        end
      end

      StRandGenerate: begin
        // The current buffer output is used as auxiliary randomness and -
        // depending on whether keccak_round is parametrized to always forward
        // the buffer output and not use intermediate randomness - forwarded
        // to the DOM multipliers without them updating in this cycle. We don't
        // need to advance the PRNG as there is no risk of accidentally
        // re-using the same randomness twice since after the current cycle:
        // - We either load and re-mask the message/key which will use
        //   different PRNG output bits. The PRNG is advanced once per 64 bits
        //   loaded.
        // - Or, the Keccak/SHA3 core is operated but it always starts with
        //   the linear layers which don't require fresh randomness. While
        //   processing the linear layers, the PRNG is advanced to have fresh
        //   randomness for the non-linear layer requiring it.
        aux_update = 1'b 1;
        rand_valid_set = 1'b 1;
        prng_en = prng_en_rand_q[0];

        st_d = StRandReady;
      end

      StRandErrWaitExpired: begin
        st_d = StRandErr;

        err_o = '{ valid: 1'b 1,
                   code: ErrWaitTimerExpired,
                   info: 24'(timer_value)
                 };
      end

      StRandErrIncorrectMode: begin
        st_d = StRandErr;

        err_o = '{ valid: 1'b 1,
                   code: ErrIncorrectEntropyMode,
                   info: 24'(mode_q)
                 };
      end

      StRandErr: begin
        // Keep entropy signal valid to complete current hashing even with error
        rand_valid_set = 1'b 1;

        // Advance the PRNG after the entropy has been used.
        prng_en = (rand_update_i | rand_consumed_i) &
            ((fast_process_i & in_keyblock_i) | ~fast_process_i);
        data_update = prng_en;

        if (err_processed_i) begin
          st_d = StRandReset;

        end else begin
          st_d = StRandErr;
        end

      end

      StTerminalError: begin
        // this state is terminal
        st_d = st;
        sparse_fsm_error_o = 1'b 1;
      end

      default: begin
        st_d = StTerminalError;
        sparse_fsm_error_o = 1'b 1;
      end
    endcase

    // SEC_CM: FSM.GLOBAL_ESC, FSM.LOCAL_ESC
    // Unconditionally jump into the terminal error state
    // if the life cycle controller triggers an escalation.
    if (lc_ctrl_pkg::lc_tx_test_true_loose(lc_escalate_en_i)) begin
      st_d = StTerminalError;
    end
  end
  `ASSERT_KNOWN(RandStKnown_A, st)

  // mubi4 sender

  assign entropy_configured = (st != StRandReset)
                            ? prim_mubi_pkg::MuBi4True
                            : prim_mubi_pkg::MuBi4False ;
  prim_mubi4_sender #(
    .AsyncOn(1'b0)
  ) u_entropy_configured (
    .clk_i,
    .rst_ni,

    .mubi_i (entropy_configured  ),
    .mubi_o (entropy_configured_o)
  );

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
