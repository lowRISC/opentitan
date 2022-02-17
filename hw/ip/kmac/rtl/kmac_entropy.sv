// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// KMAC Entropy Generation module

`include "prim_assert.sv"

module kmac_entropy
  import kmac_pkg::*; #(
  parameter lfsr_perm_t RndCnstLfsrPerm = RndCnstLfsrPermDefault,
  parameter lfsr_seed_t RndCnstLfsrSeed = RndCnstLfsrSeedDefault,

  parameter storage_perm_t RndCnstStoragePerm = RndCnstStoragePermDefault
) (
  input clk_i,
  input rst_ni,

  // EDN interface
  output logic          entropy_req_o,
  input                 entropy_ack_i,
  input  [MsgWidth-1:0] entropy_data_i,

  // Entropy to internal
  output logic                        rand_valid_o,
  output logic [sha3_pkg::StateW-1:0] rand_data_o,
  input                               rand_consumed_i,

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
  //// If 1, LFSR advances to create 64-bit PRNG. This input is used to mask the message fed into SHA3 (Keccak).
  input                       msg_mask_en_i,
  output logic [MsgWidth-1:0] lfsr_data_o,

  //// SW update of seed
  input        seed_update_i,
  input [63:0] seed_data_i,

  //// SW may initiate manual EDN seed refresh
  input entropy_refresh_req_i,

  //// Timer limit value
  //// If value is 0, timer is disabled
  input [TimerPrescalerW-1:0] wait_timer_prescaler_i,
  input [EdnWaitTimerW-1:0]   wait_timer_limit_i,

  // Status out
  //// Hash Ops counter. Count how many hashing ops (KMAC) have run
  //// after the clear request from SW
  output logic [kmac_reg_pkg::HashCntW-1:0] hash_cnt_o,
  input                                     hash_cnt_clr_i,
  input        [kmac_reg_pkg::HashCntW-1:0] hash_threshold_i,

  // Life cycle
  input  lc_ctrl_pkg::lc_tx_t lc_escalate_en_i,

  // Error output
  output err_t err_o,
  output logic sparse_fsm_error_o,
  output logic lfsr_error_o,
  output logic count_error_o,
  input        err_processed_i
);

  /////////////////
  // Definitions //
  /////////////////

  // Timer Widths are defined in kmac_pkg

  // storage width
  localparam int unsigned EntropyStorageW = 320;
  localparam int unsigned EntropyMultiply = sha3_pkg::StateW / EntropyStorageW;
  `ASSERT_INIT(StorageNoRemainder_A, (sha3_pkg::StateW%EntropyStorageW) == 0)
  `ASSERT_INIT(LfsrNoRemainder_A, (EntropyStorageW%EntropyLfsrW) == 0)

  localparam int unsigned StorageEntries = EntropyStorageW / EntropyLfsrW ;
  localparam int unsigned StorageIndexW = $clog2(StorageEntries);


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
    // this state from StRandIdle.
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

    // Expand: The SW or EDN provides 64-bit entropy (seed). In this state, this
    // entropy generator expands the 64-bit entropy into 320-bit entropy using
    // LFSR. Then it expands 320-bit pseudo random entropy into 1600-bit by
    // replicating the PR entropy five times w/ compile-time shuffling scheme.
    StRandExpand = 10'b0000001100,

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
  //// SW configures to use EDN or SEED register as a LFSR seed
  logic lfsr_seed_en;
  logic [EntropyLfsrW-1:0] lfsr_seed;
  logic lfsr_en;
  logic [EntropyLfsrW-1:0] lfsr_data;

  // storage
  logic storage_update;
  logic storage_idx_clear;
  logic storage_filled;

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

  // SEC_CM CTR.REDUN
  // This primitive is used to place a hardened counter
  prim_count #(
    .Width(kmac_reg_pkg::HashCntW),
    .OutSelDnCnt(1'b0), // 0 selects up count
    .CntStyle(prim_count_pkg::DupCnt)
  ) u_hash_count (
    .clk_i,
    .rst_ni,
    .clr_i(hash_cnt_clr),
    .set_i(1'b0),
    .set_cnt_i(kmac_reg_pkg::HashCntW'(0)),
    .en_i(hash_cnt_en),
    .step_i(kmac_reg_pkg::HashCntW'(1)),
    .cnt_o(hash_cnt_o),
    .err_o(count_error_o)
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

  // LFSR =====================================================================
  //// FSM controls the seed enable signal `lfsr_seed_en`.
  //// Seed selection
  //// Default value to entropy data_i
  assign lfsr_seed = (mode_q == EntropyModeSw) ? seed_data_i : entropy_data_i ;
  `ASSERT_KNOWN(ModeKnown_A, mode_i)

  // We employ two redundant LFSRs to guard against FI attacks.
  // If any of the two is glitched and the two LFSR states do not agree,
  // KMAC reports the fatal error via alert interface.
  // SEC_CM: PRNG.LFSR.REDUN
  prim_double_lfsr #(
    .LfsrDw(EntropyLfsrW),
    .EntropyDw(EntropyLfsrW),
    .StateOutDw(EntropyLfsrW),
    .StatePermEn(1'b1),
    .StatePerm(RndCnstLfsrPerm),
    .DefaultSeed(RndCnstLfsrSeed),
    .NonLinearOut(1'b1)
  ) u_lfsr (
    .clk_i,
    .rst_ni,
    .seed_en_i(lfsr_seed_en),
    .seed_i   (lfsr_seed),
    .lfsr_en_i(lfsr_en || msg_mask_en_i ),
    .entropy_i('0),          // Does not use additional entropy while operating
    .state_o  (lfsr_data),   // (partial) LFSR state output StateOutDw
    .err_o    (lfsr_error_o)
  );
  assign lfsr_data_o = lfsr_data; // For masking the message

  // LFSR ---------------------------------------------------------------------

  // 320-bit storage ==========================================================
  logic [EntropyStorageW-1:0] entropy_storage;
  logic [StorageIndexW-1:0] storage_idx;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      entropy_storage <= '0;
    end else if (storage_update) begin
      for (int unsigned i = 0 ; i < StorageEntries ; i++) begin
        if (StorageIndexW'(i) == storage_idx) begin
          entropy_storage[i*EntropyLfsrW+:EntropyLfsrW] <= lfsr_data;
        end
      end
    end
  end

  //// Index
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      storage_idx <= '0;
    end else if (storage_idx_clear) begin
      storage_idx <= '0;
    end else if (storage_filled) begin
      storage_idx <= storage_idx;
    end else if (storage_update) begin
      storage_idx <= storage_idx + 1'b 1;
    end
  end

  assign storage_filled = (storage_idx == StorageIndexW'(StorageEntries));
  // 320-bit storage ----------------------------------------------------------

  // Storage expands to StateW ================================================
  // May adopt fancy shuffling scheme to obsfucate
  // Or, convert the 320bit to sheet then multiply then unroll into 1600bit
  logic [sha3_pkg::StateW-1:0] rand_data_concat;
  assign rand_data_concat = {EntropyMultiply{entropy_storage}};
  // Shuffle the StateW
  always_comb begin
    rand_data_o = '0;
    for (int unsigned i = 0 ; i < sha3_pkg::StateW ; i++) begin
      rand_data_o[i] = rand_data_concat[RndCnstStoragePerm[i]];
    end
  end

  // Check if RndCnstStoragePerm < StateW
  for (genvar i = 0 ; i < sha3_pkg::StateW; i++) begin : g_storage_perm_check
    `ASSERT_INIT(RndCnstStoragePermInBound_A,
      RndCnstStoragePerm[i] < sha3_pkg::StateW)
  end

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

  `ASSUME(ConsumeNotAseertWhenNotReady_M, rand_consumed_i |-> rand_valid_o)

  // Storage expands to StateW ------------------------------------------------

  ///////////////////
  // State Machine //
  ///////////////////

  rand_st_e st, st_d;
  logic [StateWidth-1:0] st_raw_q;
  assign st = rand_st_e'(st_raw_q);

  // State FF
  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  prim_sparse_fsm_flop #(
    .StateEnumT(rand_st_e),
    .Width(StateWidth),
    .ResetValue(StateWidth'(StRandReset))
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .state_i ( st_d     ),
    .state_o ( st_raw_q )
  );

  // State: Next State and Output Logic
  // SEC_CM: FSM.SPARSE
  always_comb begin
    st_d = StRandReset;
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

    // lfsr_seed_en: Signal to update LFSR seed
    // LFSR seed can be updated by EDN or SW.
    lfsr_seed_en = 1'b 0;

    // Entropy Storage control signals
    storage_idx_clear = 1'b 0;
    storage_update    = 1'b 0;

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

        if ( (fast_process_i && in_keyblock_i && rand_consumed_i)
          || (!fast_process_i && rand_consumed_i)) begin
          // If fast_process is set, don't clear the rand valid, even
          // consumed. So, the logic does not expand the entropy again.
          // If fast_process is not set, then every rand_consume signal
          // triggers rand expansion.
          st_d = StRandExpand;

          lfsr_en           = 1'b 1;
          storage_idx_clear = 1'b 1;

          rand_valid_clear = 1'b 1;
        end else if (entropy_refresh_req_i || threshold_hit_q) begin
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
          st_d = StRandExpand;

          lfsr_en = 1'b 1;
          lfsr_seed_en = 1'b 1;

          rand_valid_clear = 1'b 1;

          storage_idx_clear = 1'b 1;
        end else if (rand_consumed_i) begin
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
        if (seed_update_i) begin
          st_d = StRandExpand;

          lfsr_en = 1'b 1;
          lfsr_seed_en = 1'b 1;

          rand_valid_clear = 1'b 1;

          storage_idx_clear = 1'b 1;
        end else begin
          st_d = StSwSeedWait;
        end
      end

      StRandExpand: begin
        lfsr_en = 1'b 1;
        if (storage_filled) begin
          st_d = StRandReady;

          storage_update = 1'b 0;

          rand_valid_set = 1'b 1;

        end else begin
          st_d = StRandExpand;

          storage_update = 1'b 1;
        end
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
                   info: 24'(mode_i)
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

    // Unconditionally jump into the terminal error state
    // if the life cycle controller triggers an escalation.
    if (lc_escalate_en_i != lc_ctrl_pkg::Off) begin
      st_d = StTerminalError;
    end
  end
  `ASSERT_KNOWN(RandStKnown_A, st)

  ////////////////
  // Assertions //
  ////////////////

  // entropy storage cannot be exceed the Entry number.
  // filled is asserted when the storage index meets the Entry number.
  // So, if filled, no update signal shall be asserted
  `ASSERT(StorageIdxInBound_A, storage_filled |-> !storage_update)

endmodule : kmac_entropy
