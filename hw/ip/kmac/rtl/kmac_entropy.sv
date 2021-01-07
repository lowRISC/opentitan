// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// KMAC Entropy Generation module

`include "prim_assert.sv"

module kmac_entropy
  import kmac_pkg::*;
(
  input clk_i,
  input rst_ni,

  // EDN interface
  output logic          entropy_req_o,
  input                 entropy_ack_i,
  input  [MsgWidth-1:0] entropy_data_i,

  // Entropy to internal
  output logic                  rand_valid_o,
  output [sha3_pkg::StateW-1:0] rand_data_o,
  input                         rand_consumed_i,

  // Status
  input in_progress_i,
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

  //// SW update of seed
  input        seed_update_i,
  input [63:0] seed_data_i,

  //// Timer limit value
  //// If value is 0, timer is disabled
  input [EntropyTimerW-1:0] entropy_timer_limit_i,
  input [EdnWaitTimerW-1:0] wait_timer_limit_i,

  // Error output
  output err_t err_o,
  input        err_processed_i
);

  /////////////////
  // Definitions //
  /////////////////

  // Timer Widths are defined in kmac_pkg

  // storage width
  localparam int unsigned EntropyLfsrW    = 64;
  localparam int unsigned EntropyStorageW = 320;
  localparam int unsigned EntropyMultiply = sha3_pkg::StateW / EntropyStorageW;
  `ASSERT_INIT(StorageNoRemainder_A, (sha3_pkg::StateW%EntropyStorageW) == 0)
  `ASSERT_INIT(LfsrNoRemainder_A, (EntropyStorageW%EntropyLfsrW) == 0)

  localparam int unsigned StorageEntries = EntropyStorageW / EntropyLfsrW ;
  localparam int unsigned StorageIndexW = $clog2(StorageEntries);

  // States
  typedef enum logic [3:0] {
    // Reset: Reset state. The entropy is not ready. The state machine should
    // get new entropy from EDN or the seed should be feeded by the software.
    StRandReset,

    // The seed is fed into LFSR and the entropy is ready. It means the
    // rand_valid is asserted with valid data. It takes a few steps to reach
    // this state from StRandIdle.
    StRandReady,

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
    StRandEdn,

    // Sw Seed: If mode is set to manual mode, This entropy module needs initial
    // seed from the software. It waits the seed update signal to expand initial
    // entropy
    StSwSeedWait,

    // Expand: The SW or EDN provides 64-bit entropy (seed). In this state, this
    // entropy generator expands the 64-bit entropy into 320-bit entropy using
    // LFSR. Then it expands 320-bit pseudo random entropy into 1600-bit by
    // replicating the PR entropy five times w/ compile-time shuffling scheme.
    StRandExpand,

    // ErrWaitExpired: If Edn timer expires, FSM moves to this state and wait
    // the software response. Software should switch to manual mode then disable
    // the timer (to 0) and update the seed via register interface.
    StRandErrWaitExpired,

    // ErrNoValidMode: If SW sets entropy ready but the mode is not either
    // Manual Mode nor EdnMode, this logic reports to SW with
    // NoValidEntropyMode.
    StRandErrIncorrectMode,

    // Err: After the error is reported, FSM sits in Err state ignoring all the
    // requests. It does not generate new entropy and drops the entropy valid
    // signal.
    //
    // SW sets err_processed signal to clear the error. The software should
    // clear the entropy ready signal before clear the error interrupt so that
    // the FSM sits in StRandReset state not moving forward with incorrect
    // configurations.
    StRandErr
  } rand_st_e;

  /////////////
  // Signals //
  /////////////

  // Timers
  // "Entropy Timer": While in operation, if this entropy timer is enabled, FSM
  //   fetches new entropy from LFSR when the timer is expired.
  //
  // "Wait Timer": This timer is in active when FSM sends entropy request to EDN
  //   If EDN does not return the entropy data until the timer expired, FSM
  //   moves to error state and report the error to the system.

  typedef enum logic [1:0] {
    NoTimer      = 2'h 0,
    EntropyTimer = 2'h 1,
    EdnWaitTimer = 2'h 2
  } timer_sel_e;
  timer_sel_e timer_sel;

  localparam int unsigned TimerW = (EntropyTimerW > EdnWaitTimerW)
                                 ? EntropyTimerW : EdnWaitTimerW;
  logic timer_enable, timer_update, timer_expired;
  logic [TimerW-1:0] timer_limit;
  logic [TimerW-1:0] timer_value;

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

  // in_progress: check if in_progress de-asserted. It means hashing operation
  // is completed. Entropy logic refreshes seed and prepare new entropy.
  // de-asserting in_progress sets in_progress_deasserted, then when FSM moves
  // to StRandEdn, it clears the de-assertion. This is to not miss the
  // deassertion event.
  logic in_progress_deasserted, in_progress_clear, in_progress_d;

  // Entropy valid signal
  // FSM set and clear the valid signal, rand_consume signal clear the valid
  // signal. Split the set, clear to make entropy valid while FSM is processing
  // other tasks.
  logic rand_valid_set, rand_valid_clear;

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
    end else if (timer_enable && |timer_value) begin // if non-zero timer v
      timer_value <= timer_value - 1'b 1;
    end
  end

  // select timer
  always_comb begin
    timer_limit = '0;
    unique case (timer_sel)
      EntropyTimer: timer_limit = TimerW'(entropy_timer_limit_i);
      EdnWaitTimer: timer_limit = TimerW'(wait_timer_limit_i);
      default: timer_limit = '0; // NoTimer
    endcase
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      timer_expired <= 1'b 0;
    end else if (timer_update) begin
      timer_expired <= 1'b 0;
    end else if (timer_enable && (timer_value == '0)) begin
      timer_expired <= 1'b 1;
    end
  end
  // Timers -------------------------------------------------------------------


  // LFSR =====================================================================
  //// FSM controls the seed enable signal `lfsr_seed_en`.
  //// Seed selection
  always_comb begin
    unique case (mode_i)
      EntropyModeNone: lfsr_seed = '0;
      // TODO: Check EDN Bus width
      EntropyModeEdn:  lfsr_seed = entropy_data_i;
      EntropyModeSw:   lfsr_seed = seed_data_i;
      default:         lfsr_seed = '0;
    endcase
  end
  `ASSERT_KNOWN(ModeKnown_A, mode_i)

  prim_lfsr #(
    .LfsrDw(EntropyLfsrW),
    .EntropyDw(EntropyLfsrW),
    .StateOutDw(EntropyLfsrW)
  ) u_lfsr (
    .clk_i,
    .rst_ni,
    .seed_en_i(lfsr_seed_en),
    .seed_i   (lfsr_seed),
    .lfsr_en_i(lfsr_en),
    .entropy_i('0),        // Does not use additional entropy while operating
    .state_o  (lfsr_data)  // (partial) LFSR state output StateOutDw
  );
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
    // TODO: Should the consumed entropy be discarded?
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
  assign rand_data_o = {EntropyMultiply{entropy_storage}};

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

  // In Process Logic =========================================================
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      in_progress_d <= 1'b 0;
    end else begin
      in_progress_d <= in_progress_i;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      in_progress_deasserted <= 1'b 0;
    end else if (in_progress_d && !in_progress_i && (mode_i == EntropyModeEdn)) begin
      in_progress_deasserted <= 1'b 1;
    end else if (in_progress_clear) begin
      in_progress_deasserted <= 1'b 0;
    end
  end
  // In Process Logic ---------------------------------------------------------

  ///////////////////
  // State Machine //
  ///////////////////

  rand_st_e st, st_d;

  // State FF
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      st <= StRandReset;
    end else begin
      st <= st_d;
    end
  end

  // State: Next State and Output Logic
  always_comb begin
    st_d = StRandReset;

    // Default Timer values
    timer_enable = 1'b 0;
    timer_update = 1'b 0;
    timer_sel    = NoTimer;

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

    // lfsr_en: Let LFSR run
    // To save power, this logic enables LFSR when it needs entropy expansion.
    // TODO: Check if random LFSR run while staying in ready state to obsfucate
    // LFSR value?
    lfsr_en = 1'b 0;

    // lfsr_seed_en: Signal to update LFSR seed
    // LFSR seed can be updated by EDN or SW.
    lfsr_seed_en = 1'b 0;

    // Entropy Storage control signals
    storage_idx_clear = 1'b 0;
    storage_update    = 1'b 0;

    in_progress_clear = 1'b 0;

    // Error
    err_o = '{valid: 1'b 0, code: ErrNone, info: '0};

    unique case (st)
      StRandReset: begin
        if (entropy_ready_i) begin
          // SW has configured KMAC
          unique case (mode_i)
            EntropyModeSw: begin
              st_d = StSwSeedWait;
            end

            EntropyModeEdn: begin
              st_d = StRandEdn;

              // Timer reset
              timer_sel = EdnWaitTimer;
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
        end else if (mode_i == EntropyModeEdn) begin
          if (in_keyblock_i && timer_expired && |entropy_timer_limit_i) begin
            // Timer count is non-zero and timer expired
            st_d = StRandEdn;

            timer_update = 1'b 1;
            timer_sel    = EdnWaitTimer;

          end else if (in_progress_deasserted) begin
            // hashing operation is completed, refresh the entropy and stop
            st_d = StRandEdn;

            in_progress_clear = 1'b 1;

            timer_update = 1'b 1;
            timer_sel    = EdnWaitTimer;
          end else begin
            st_d = StRandReady;
          end
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
          // TODO: check fips?
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

          // Based on the timer value, either reset the timer or just move
          if (mode_i == EntropyModeEdn && |entropy_timer_limit_i) begin
            timer_sel = EntropyTimer;
            timer_update = 1'b 1;
          end
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

          // TODO: Reset as much as
        end else begin
          st_d = StRandErr;
        end

      end

      default: begin
        st_d = StRandReset;
      end
    endcase
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

