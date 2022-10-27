// Copyright lowRISC contributors.
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
  parameter lfsr_fwd_perm_t RndCnstLfsrFwdPerm = RndCnstLfsrFwdPermDefault
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

  //// LFSR Enable for Message Masking
  //// If 1, LFSR advances to create 64-bit PRNG. This input is used to mask
  //// the message fed into SHA3 (Keccak).
  input                       msg_mask_en_i,
  output logic [MsgWidth-1:0] msg_mask_o,

  //// SW update of seed
  input [NumSeedsEntropyLfsr-1:0]       seed_update_i,
  input [NumSeedsEntropyLfsr-1:0][31:0] seed_data_i,

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

    // The seed is fed into LFSR and the entropy is ready. It means the
    // rand_valid is asserted with valid data. It takes a few steps to reach
    // this state from StRandReset.
    StRandReady = 10'b0110000100,

    // EDN interface: Send request and receive
    // RandEdnReq state can be transit from StRandReset or from StRandReady
    //
    // Reset --> EdnReq:
    //     If entropy source module is ready, the software sets a bit in CFG
    //     also sets the entropy mode to EdnMode. Then this FSM moves to EdnReq
    //     to initialize LFSR seed.
    //
    // Ready --> EdnReq:
    //     1. If a mode is configured as to update entropy everytime it is
    //        consumed, then the FSM moves from Ready to EdnReq to refresh seed
    //     2. If the software enabled EDN timer and the timer is expired and
    //        also the KMAC is processing the key block, the FSM moves to
    //        EdnReq to refresh seed
    //     3. If a KMAC operation is completed, the FSM also refreshes the LFSR
    //        seed to prepare next KMAC op or wipe out operation.
    StRandEdn = 10'b1100100111,

    // Sw Seed: If mode is set to manual mode, This entropy module needs initial
    // seed from the software. It waits the seed update signal to expand initial
    // entropy
    StSwSeedWait = 10'b1011110110,

    // Generate: In this state, the entropy generator advances the LFSRs to
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

  // LFSR
  // SW configures to use EDN or SEED register as a LFSR seed
  logic [NumSeedsEntropyLfsr-1:0]                            lfsr_seed_en_red;
  logic [NumChunksEntropyLfsr-1:0]                           lfsr_seed_en;
  logic [NumChunksEntropyLfsr-1:0][ChunkSizeEntropyLfsr-1:0] lfsr_seed;
  logic lfsr_seed_done;
  logic lfsr_en;
  logic [NumChunksEntropyLfsr-1:0][ChunkSizeEntropyLfsr-1:0] lfsr_data_chunked;
  logic [EntropyLfsrW-1:0] lfsr_data, lfsr_data_permuted;

  // Auxliliary randomness
  logic aux_rand_d, aux_rand_q;
  logic aux_update;

  // Randomness for controlling PRNG updates. This only matters for clock cycles
  // where the PRNG output is not actually used.
  logic [3:0] lfsr_en_rand_d, lfsr_en_rand_q;

  // Entropy valid signal
  // FSM set and clear the valid signal, rand_consume signal clear the valid
  // signal. Split the set, clear to make entropy valid while FSM is processing
  // other tasks.
  logic rand_valid_set, rand_valid_clear;

  // Signal to track whether the FSM should stay in the StRandReady state or
  // move to StRandGenerate upon getting the next rand_consumed_i.
  logic ready_phase_d, ready_phase_q;

  // FSM latches the mode and stores into mode_q when the FSM is out from
  // StReset. The following states, or internal datapath uses mode_q after that.
  // If the SW wants to change the mode, it requires resetting the IP.
  logic mode_latch;
  entropy_mode_e mode_q;

  // Status out: entropy configured
  prim_mubi_pkg::mubi4_t entropy_configured;

  //////////////
  // Datapath //
  //////////////

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
      prescaler_cnt <= wait_timer_prescaler_i;
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
    .cnt_o(hash_cnt_o),
    .cnt_next_o(),
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

  // LFSRs ====================================================================

  // We use 25 32-bit LFSRs in parallel to generate the 800 bits of randomness
  // required by the DOM multipliers inside the Keccak core in a single clock
  // cycle. To reduce the entropy consumption for periodic reseeding, a cascaded
  // reseeding mechanism is used:
  //
  // - LFSR 0 (5/10/15/20) gets one 32-bit seed each from EDN/SW.
  // - LFSR 1 (6/11/16/21) gets the old state of LFSR 0 (5/10/15/20)
  // - ...
  // - LFSR 4 (9/14/19/24) gets the old state of LFSR 3 (8/13/18/23)
  //
  // In addition, the forwarded old states are permuted.
  //
  // This allows to reduce the entropy consumption. A full reseed of all 25
  // LFSRs is still possible by subsequently triggering 5 reseeding operations
  // though software.

  // Reseeding counter - We reseed one 32-bit chunk at a time and need to keep
  // track of which LFSR chunk to reseed next.
  localparam int unsigned SeedIdxWidth =
      prim_util_pkg::vbits(NumSeedsEntropyLfsr);
  logic [SeedIdxWidth-1:0] seed_idx;
  logic seed_idx_count_error;

  // SEC_CM CTR.REDUN
  // This primitive is used to place a hardened counter
  prim_count #(
    .Width(SeedIdxWidth)
  ) u_seed_idx_count (
    .clk_i,
    .rst_ni,
    .clr_i(lfsr_seed_done),
    .set_i(1'b0),
    .set_cnt_i(SeedIdxWidth'(0)),
    .incr_en_i(|lfsr_seed_en),
    .decr_en_i(1'b0),
    .step_i(SeedIdxWidth'(1)),
    .cnt_o(seed_idx),
    .cnt_next_o(),
    .err_o(seed_idx_count_error)
  );

  assign lfsr_seed_done =
      (seed_idx == SeedIdxWidth'(unsigned'(NumSeedsEntropyLfsr - 1))) &
      |lfsr_seed_en;

  // Seed selection - The reduced seed enable signal `lfsr_seed_en_red` is
  // controlled by the FSM. Here we just repliate it as we're always reseeding
  // 5 LFSRs together.
  for (genvar i = 0; i < 5; i++) begin : gen_lfsr_seed_en
    assign lfsr_seed_en[i * 5 +: 5] = {5{lfsr_seed_en_red[i]}};
  end

  // From software we get NumChunks 32-bit seeds but only one is valid. The
  // others may be zero.
  // From EDN we get a single 32-bit seed. This is the default value forwarded.
  for (genvar i = 0; i < NumSeedsEntropyLfsr; i++) begin : gen_lfsr_seed
    // LFSRs 0/5/10/15/20 get the fresh entropy.
    assign lfsr_seed[i * 5] =
        (mode_q == EntropyModeSw) ? seed_data_i[i] : entropy_data_i;

    // The other LFSRs get the permuted old states.
    for (genvar j = 0; j < 4; j++) begin : gen_fwd_seeds
      for (genvar k = 0; k < ChunkSizeEntropyLfsr; k++) begin : gen_fwd_perm
        assign lfsr_seed[i * 5 + j + 1][k] =
            lfsr_data_chunked[i * 5 + j][RndCnstLfsrFwdPerm[k]];
      end
    end
  end
  `ASSERT_KNOWN(ModeKnown_A, mode_i)

  // We employ five 32-bit LFSRs to generate 160 bits per clock cycle. Using
  // multiple 32-bit LFSRs with an additional permutation layer spanning across
  // all LFSRs has relevant advantages:
  // - Multiple simulateneous faults needs to be injected to get a fully
  //   deterministic output.
  // - No additional buffering is needed for reseeding. Both software and EDN
  //   provide 32 bits at a time meaning we can reseed the LFSRs directly as
  //   we get the entropy.
  // We use multiple LFSR instances each having a width of ChunkSize.
  for (genvar i = 0; i < NumChunksEntropyLfsr; i++) begin : gen_lfsrs
    prim_lfsr #(
      .LfsrType("GAL_XOR"),
      .LfsrDw(ChunkSizeEntropyLfsr),
      .StateOutDw(ChunkSizeEntropyLfsr),
      .DefaultSeed(RndCnstLfsrSeed[i * ChunkSizeEntropyLfsr +: ChunkSizeEntropyLfsr]),
      .StatePermEn(1'b0),
      .NonLinearOut(1'b1)
    ) u_lfsr_chunk (
      .clk_i,
      .rst_ni,
      .seed_en_i(lfsr_seed_en[i]),
      .seed_i   (lfsr_seed[i]),
      .lfsr_en_i(lfsr_en || msg_mask_en_i),
      .entropy_i('0),
      .state_o  (lfsr_data_chunked[i])
    );
  end

  // Add a permutation layer spanning across all LFSRs to break linear shift
  // patterns.
  assign lfsr_data = lfsr_data_chunked;
  for (genvar i = 0; i < EntropyLfsrW; i++) begin : gen_perm
    assign lfsr_data_permuted[i] = lfsr_data[RndCnstLfsrPerm[i]];
  end

  // Forwrad LSBs for masking the message.
  assign msg_mask_o = lfsr_data_permuted[MsgWidth-1:0];

  // LFSRs --------------------------------------------------------------------

  // Auxiliary randomness =====================================================
  assign aux_rand_d = aux_update ? lfsr_data_permuted[EntropyLfsrW - 1] :
                                   aux_rand_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      aux_rand_q <= '0;
    end else begin
      aux_rand_q <= aux_rand_d;
    end
  end

  // Auxiliary randomness -----------------------------------------------------

  // LFSR enable randomness ===================================================
  assign lfsr_en_rand_d =
      aux_update ? lfsr_data_permuted[EntropyLfsrW - 2 -: 4] : // refresh
                   {1'b0, lfsr_en_rand_q[3:1]};                // shift out

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      lfsr_en_rand_q <= '0;
    end else begin
      lfsr_en_rand_q <= lfsr_en_rand_d;
    end
  end

  // LFSR enable randomness ---------------------------------------------------

  // Randomness outputs =======================================================
  assign rand_data_o = lfsr_data_permuted;
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

  `ASSUME(ConsumeNotAseertWhenNotReady_M, rand_consumed_i |-> rand_valid_o)

  // Randomness outputs -------------------------------------------------------

  // Remaining outputs
  assign count_error_o = hash_count_error | seed_idx_count_error;

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

    // EDN request
    entropy_req_o = 1'b 0;

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

    // lfsr_en: Let LFSR run
    // To save power, this logic enables LFSR when it needs entropy expansion.
    lfsr_en = 1'b 0;

    // lfsr_seed_en_red: Signal to update LFSR seed
    // LFSR seed can be updated by EDN or SW.
    lfsr_seed_en_red = '0;

    // Signal to track whether FSM should stay in StRandReady state or move on.
    ready_phase_d = ready_phase_q;

    // Auxiliary randomness control signals
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
              st_d = StSwSeedWait;
            end

            EntropyModeEdn: begin
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

        lfsr_en = lfsr_en_rand_q[0];

        if (rand_consumed_i &&
            ((fast_process_i && in_keyblock_i) || !fast_process_i)) begin
          // If fast_process is set, don't clear the rand valid, even
          // consumed. So, the logic does not expand the entropy again.
          // If fast_process is not set, then every rand_consume signal
          // triggers rand expansion.

          // Allow for two reads from the Keccak core. This is what is needed
          // per round.
          lfsr_en = 1'b 1;
          ready_phase_d = ~ready_phase_q;

          if (ready_phase_q) begin
            st_d = StRandGenerate;

            rand_valid_clear = 1'b 1;
          end else begin
            st_d = StRandReady;
          end
        end else if ((mode_q == EntropyModeEdn) &&
            (entropy_refresh_req_i || threshold_hit_q)) begin
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
        // Send request
        entropy_req_o = 1'b 1;

        // Wait timer
        timer_enable = 1'b 1;

        if (timer_expired && |wait_timer_limit_i) begin
          // If timer count is non-zero and expired;
          st_d = StRandErrWaitExpired;

        end else if (entropy_ack_i) begin
          lfsr_seed_en_red[seed_idx] = 1'b 1;

          if (lfsr_seed_done) begin
            st_d = StRandGenerate;

            if ((fast_process_i && in_keyblock_i) || !fast_process_i) begin
              lfsr_en = 1'b 1;
              rand_valid_clear = 1'b 1;
            end
          end else begin
            st_d = StRandEdn;
          end
        end else if (rand_consumed_i &&
            ((fast_process_i && in_keyblock_i) || !fast_process_i)) begin
          // Somehow, while waiting the EDN entropy, the KMAC or SHA3 logic
          // consumed the remained entropy. This can happen when the previous
          // SHA3/ KMAC op completed and this Entropy FSM has moved to this
          // state to refresh the entropy and the SW initiates another hash
          // operation while waiting for the EDN response.
          st_d = StRandEdn;

          rand_valid_clear = 1'b 1;
        end else begin
          st_d = StRandEdn;
        end
      end

      StSwSeedWait: begin
        lfsr_seed_en_red = seed_update_i;

        if (lfsr_seed_done) begin
          st_d = StRandGenerate;

          lfsr_en = 1'b 1;

          rand_valid_clear = 1'b 1;
        end else begin
          st_d = StSwSeedWait;
        end
      end

      StRandGenerate: begin
        // The current LFSR output is used as auxiliary randomness.
        aux_update = 1'b 1;

        // Advance the LFSR and set the valid bit. The next LFSR output will be
        // used for re-masking.
        lfsr_en = 1'b 1;
        rand_valid_set = 1'b 1;

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
    if (lc_escalate_en_i != lc_ctrl_pkg::Off) begin
      st_d = StTerminalError;
    end
  end
  `ASSERT_KNOWN(RandStKnown_A, st)

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      ready_phase_q <= '0;
    end else begin
      ready_phase_q <= ready_phase_d;
    end
  end

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

  `ASSERT_INIT(EntropyLfsrWDivisble, NumChunksEntropyLfsr ==
      EntropyLfsrW / ChunkSizeEntropyLfsr)

  // We reseed one chunk of the entropy generator at a time. Therefore the
  // chunk size must match the data width of the software and EDN inputs.
  `ASSERT_INIT(ChunkSizeEntropyLfsrMatchesSw, ChunkSizeEntropyLfsr == 32)
  `ASSERT_INIT(ChunkSizeEntropyLfsrMatchesEdn, ChunkSizeEntropyLfsr ==
      edn_pkg::ENDPOINT_BUS_WIDTH)

// the code below is not meant to be synthesized,
// but it is intended to be used in simulation and FPV
`ifndef SYNTHESIS
  // Check that the supplied permutations are valid.
  logic [EntropyLfsrW-1:0] perm_test;
  initial begin : p_perm_check
    perm_test = '0;
    for (int k = 0; k < EntropyLfsrW; k++) begin
      perm_test[RndCnstLfsrPerm[k]] = 1'b1;
    end
    // All bit positions must be marked with 1.
    `ASSERT_I(PermutationCheck_A, &perm_test)
  end

  logic [ChunkSizeEntropyLfsr-1:0] perm_fwd_test;
  initial begin : p_perm_fwd_check
    perm_fwd_test = '0;
    for (int k = 0; k < ChunkSizeEntropyLfsr; k++) begin
      perm_fwd_test[RndCnstLfsrFwdPerm[k]] = 1'b1;
    end
    // All bit positions must be marked with 1.
    `ASSERT_I(PermutationCheck_A, &perm_fwd_test)
  end
`endif

endmodule : kmac_entropy
