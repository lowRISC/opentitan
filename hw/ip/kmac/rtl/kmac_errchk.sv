// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// KMAC Error Checking logic
//
// `kmac_err` module checks the SW introduced errors.
//  1. SW command sequencing error.
//  2. SW configuration error.
//
// ## SW Command Sequencing Error
//
// KMAC assumes the application interface and the SW register interface to
// follow the specific sequence. It expects the requester to send the `Start`
// command then push the message body. The `Process` command follows the message
// body. The SW may issue `Run` command if it needs the digest result more than
// a block rate. Then SW completes the hash operation with `Done` command.
//
// This `kmac_err` module checks if the SW issues the correct command. If not,
// it reports the error via ERR_CODE register.
//
// However, the logic does not prevent the error-ed command to be propagated.
// The unexpected commands are filtered by each individual submodule.
//
// st := { Idle, StateWrite, MsgFeed, Processing, Absorbed, Stopped, Squeeze}
//
// allowed := {
//   Idle :      { Start, StateWrite },
//   StateWrite: { Continue, Done    },
//   MsgFeed:    { Process, Stop     },
//   Processing: { None              },
//   Absorbed:   { Run, Done         },
//   Stopped:    { Done              },
//   Squeeze:    { None              }
// }
//
// A context can be resumed with issuing first `StateWrite` to claim the
// KMAC HWIP and write the state. Then, the `Continue` command is used to
// proceed with this context.
//
// ## SW Configuration Error
//
// `kmac_errchk` module checks if SW configured correct combinations of the
// configuration registers when the hashing operation begins.
//
// 1. Mode & Strength combinations
// 2. Kmac Prefix
// 3. Sideload when saving or restoring a context
// * sideload & key_valid -> Checker in kmac_core

`include "prim_assert.sv"

module kmac_errchk
  import kmac_pkg::*;
  import sha3_pkg::sha3_mode_e;
  import sha3_pkg::keccak_strength_e;
#(
  parameter bit EnMasking = 1'b 1
) (
  input clk_i,
  input rst_ni,

  // Configurations
  input sha3_mode_e       cfg_mode_i,
  input keccak_strength_e cfg_strength_i,

  input        kmac_en_i,
  input        cfg_sideload_i,
  input [47:0] cfg_prefix_6B_i, // first 6B of PREFIX

  // If the signal below is set, errchk propagates the command to the rest of
  // the blocks even with err_modestrength.
  input        cfg_en_unsupported_modestrength_i,

  // Entropy Ready Status to check if SW initiated the hash without entropy cfg
  input        entropy_ready_pulse_i,

  // SW commands: Only valid command is sent out to the rest of the modules
  input  kmac_cmd_e sw_cmd_i,
  output kmac_cmd_e sw_cmd_o,

  // Status from KMAC_APP
  input app_active_i,

  // Status from SHA3 core
  input prim_mubi_pkg::mubi4_t sha3_absorbed_i,
  input prim_mubi_pkg::mubi4_t sha3_stopped_i,
  input                        sha3_stop_error_i,
  input                        state_restored_i,
  input keccak_done_i,

  // Life cycle
  input  lc_ctrl_pkg::lc_tx_t lc_escalate_en_i,

  // Error processed indicator
  input err_processed_i,

  input prim_mubi_pkg::mubi4_t clear_after_error_i,

  output err_t error_o,
  output logic sparse_fsm_error_o
);

  // sha3_pkg::sha3_mode_e
  import sha3_pkg::L128;
  import sha3_pkg::L224;
  import sha3_pkg::L256;
  import sha3_pkg::L384;
  import sha3_pkg::L512;

  // sha3_pkg::keccak_strength_e
  import sha3_pkg::Sha3;
  import sha3_pkg::Shake;
  import sha3_pkg::CShake;

  /////////////////
  // Definitions //
  /////////////////
  // Encoding generated at commit 6852a91493 using Python 3.12.13 with:
  // $ ./util/design/sparse-fsm-encode.py --language=sv --avoid-zero \
  //     --seed 52166682 --distance 3 --states 8 --bits 7
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (42.86%)
  //  4: |||||||||||||||||| (39.29%)
  //  5: ||||| (10.71%)
  //  6: ||| (7.14%)
  //  7: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 6
  // Minimum Hamming weight: 3
  // Maximum Hamming weight: 5
  //
  localparam int StateWidth = 7;
  typedef enum logic [StateWidth-1:0] {
    StIdle = 7'b0111010,
    StStateWrite = 7'b1110001,
    StMsgFeed = 7'b0111101,
    StProcessing = 7'b1011011,
    StAbsorbed = 7'b1110110,
    StStopped = 7'b0000111,
    StSqueezing = 7'b1101000,
    StTerminalError = 7'b1001110
  } st_e;
  st_e st, st_d;

  localparam int StateWidthL = 3;
  typedef enum logic [StateWidthL-1:0] {
    StIdleL,
    StStateWriteL,
    StMsgFeedL,
    StProcessingL,
    StAbsorbedL,
    StStoppedL,
    StSqueezingL,
    StErrorL
  } st_logical_e;
  st_logical_e stL;


  /////////////
  // Signals //
  /////////////

  // `err_swsequence` occurs when SW issues wrong command
  logic err_swsequence;

  // `err_modestrength` occurs when Mode & Strength combinations are not
  // allowed. This error does not block the hashing operation.
  // UnexpectedModeStrength may stop the processing based on CFG
  // The error raises when SW issues CmdStart.
  logic err_modestrength;

  // `err_prefix` occurs when the first 6B of !!PREFIX is not
  // `encode_string("KMAC")` and kmac is enabled. This error does not block the
  // KMAC operation.
  logic err_prefix;

  // `err_entropy_ready` occurs when SW initiated the hashing op. without
  // configuring the entropy. This error may happen only when EnMasking is
  // set.
  logic err_entropy_ready;

  // entropy_ready is a pulse signal. Logic needs to store the state.
  logic cfg_entropy_ready;

  // `err_sideload` occurs when SW requests a context switch while the
  // sideloaded key is selected. Saving the context would expose the
  // intermediate state of a key that SW does not know. This error blocks the
  // command.
  logic err_sideload;

  // `err_continue_no_context` occurs when SW resumes an absorb without
  // restoring the context before.
  logic err_continue_no_context;

  // Signal to block the SW command propagation
  logic block_swcmd;

  ///////////////////
  // Error Checker //
  ///////////////////

  // SW sequence Error
  // info field: Current state, Received command
  // SEC_CM: FSM.SPARSE
  always_comb begin
    err_swsequence = 1'b 0;
    sparse_fsm_error_o = 1'b 0;

    unique case (st)
      StIdle: begin
        // Allow Start and StateWrite command only
        if (!(sw_cmd_i inside {CmdNone, CmdStart, CmdStateWrite})) begin
          err_swsequence = 1'b 1;
        end
      end

      StStateWrite: begin
        // Allow Continue to resume the restored context, and Done to release
        // the block again without resuming.
        if (!(sw_cmd_i inside {CmdNone, CmdContinue, CmdDone})) begin
          err_swsequence = 1'b 1;
        end
      end

      StMsgFeed: begin
        // Allow Process and Stop only
        if (!(sw_cmd_i inside {CmdNone, CmdProcess, CmdStop})) begin
          err_swsequence = 1'b 1;
        end
      end

      StProcessing: begin
        if (sw_cmd_i != CmdNone) begin
          err_swsequence = 1'b 1;
        end
      end

      StAbsorbed: begin
        // Allow ManualRun and Done
        if (!(sw_cmd_i inside {CmdNone, CmdManualRun, CmdDone})) begin
          err_swsequence = 1'b 1;
        end
      end

      StStopped: begin
        // Allow Done only
        if (!(sw_cmd_i inside {CmdNone, CmdDone})) begin
          err_swsequence = 1'b 1;
        end
      end

      StSqueezing: begin
        if (sw_cmd_i != CmdNone) begin
          err_swsequence = 1'b 1;
        end
      end

      StTerminalError: begin
        err_swsequence = 1'b 0;
        sparse_fsm_error_o = 1'b 1;
      end

      default: begin
        err_swsequence = 1'b 0;
        sparse_fsm_error_o = 1'b 1;
      end
    endcase
  end

  // A context switch is not allowed when a sideloaded key is used.
  assign err_sideload = cfg_sideload_i && (sw_cmd_i inside {CmdStop, CmdStateWrite, CmdContinue});

  // An absorb can only be resumed after a context has been restored.
  assign err_continue_no_context = (sw_cmd_i == CmdContinue) && !state_restored_i;

  assign block_swcmd =  (err_swsequence)
                     || (err_modestrength
                         && !cfg_en_unsupported_modestrength_i)
                     || err_entropy_ready
                     || err_sideload
                     || err_continue_no_context;

  // sw_cmd_o latch
  // To reduce the command path delay, sw_cmd is latched here
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)           sw_cmd_o <= CmdNone;
    else if (!block_swcmd) sw_cmd_o <= sw_cmd_i;
  end

  // Mode & Strength
  always_comb begin : check_modestrength
    err_modestrength = 1'b 0;

    if (st == StIdle && st_d == StMsgFeed) begin
      // When moving to the next stage, checks the config
      if (!((cfg_mode_i == Sha3 &&
             cfg_strength_i inside {L224, L256, L384, L512}) ||
            ((cfg_mode_i == Shake || cfg_mode_i == CShake) &&
             (cfg_strength_i inside {L128, L256})))) begin
        err_modestrength = 1'b 1;
      end
    end
  end : check_modestrength


  // Check prefix 6B is `encode_string("KMAC")`
  always_comb begin : check_prefix
    err_prefix = 1'b 0;

    if (st == StIdle && st_d == StMsgFeed && kmac_en_i) begin
      if (cfg_prefix_6B_i != EncodedStringKMAC) begin
        err_prefix = 1'b 1;
      end
    end
  end : check_prefix

  if (EnMasking) begin : g_entropy_chk

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni)              cfg_entropy_ready <= 1'b 0;
      else if (err_processed_i) cfg_entropy_ready <= 1'b 0;
      else if (entropy_ready_pulse_i && st == StIdle) begin
        cfg_entropy_ready <= 1'b 1;
      end
    end

    always_comb begin : check_entropy_ready
      err_entropy_ready = 1'b 0;

      if (st == StIdle && st_d == StMsgFeed && kmac_en_i) begin
        if (!cfg_entropy_ready) begin
          err_entropy_ready = 1'b 1;
        end
      end
    end : check_entropy_ready

  end else begin : g_pseudo_entropy_chk

    // If EnMasking is 0, entropy module is not generated.
    // tying the error signal to 0.
    assign err_entropy_ready = 1'b 0;

    assign cfg_entropy_ready = 1'b 1;

    logic unused_cfg_entropy_ready;
    assign unused_cfg_entropy_ready = cfg_entropy_ready;

    logic unused_err_processed;
    assign unused_err_processed = err_processed_i;

    logic unused_entropy_ready_puls;
    assign unused_entropy_ready_puls = entropy_ready_pulse_i;

  end

  always_comb begin : recode_st
    unique case (st)
      StIdle       : stL = StIdleL;
      StStateWrite : stL = StStateWriteL;
      StMsgFeed    : stL = StMsgFeedL;
      StProcessing : stL = StProcessingL;
      StAbsorbed   : stL = StAbsorbedL;
      StStopped    : stL = StStoppedL;
      StSqueezing  : stL = StSqueezingL;
      default      : stL = StErrorL;
    endcase
  end : recode_st

  // Return error code
  err_t err;
  always_comb begin : err_return
    err = '{valid: 1'b0, code: ErrNone, info: '0};

    priority case (1'b 1)
      err_sideload: begin
        err = '{ valid: 1'b 1,
                 code:  ErrSwSaveRestoreSideload,
                 info:  24'({2'b 0, sw_cmd_i})
               };
      end

      err_continue_no_context: begin
        err = '{ valid: 1'b 1,
                 code:  ErrSwContinueWithoutContext,
                 info:  24'({5'h 0, stL})
               };
      end

      sha3_stop_error_i: begin
        err = '{ valid: 1'b 1,
                 code:  ErrSwStopNotBlockAligned,
                 info:  24'({5'h 0, stL})
               };
      end

      err_swsequence: begin
        err = '{ valid: 1'b 1,
                 code: ErrSwCmdSequence,
                 info: {5'h0,
                        {err_swsequence, err_modestrength, err_prefix},
                        {5'h 0, stL},
                        {2'b0, sw_cmd_i}
                       }
               };
      end

      err_modestrength: begin
        err = '{ valid: 1'b 1,
                 code:  ErrUnexpectedModeStrength,
                 info:  { 5'h 0,
                          {err_swsequence, err_modestrength, err_prefix},
                          8'h 0,
                          {2'b 00, cfg_mode_i},
                          {1'b 0,  cfg_strength_i}
                        }
               };
      end

      err_prefix: begin
        err = '{ valid: 1'b 1,
                 code:  ErrIncorrectFunctionName,
                 info:  { 5'h 0,
                          {err_swsequence, err_modestrength, err_prefix},
                          16'h 0000
                        }
               };
      end

      err_entropy_ready: begin
        err = '{ valid: 1'b 1,
                 code:  ErrSwHashingWithoutEntropyReady,
                 info:  { 8'({ err_entropy_ready,
                               err_swsequence,
                               err_modestrength,
                               err_prefix}),
                          16'({kmac_en_i, cfg_entropy_ready})
                        }
               };
      end

      default: begin
        err = '{valid: 1'b0, code: ErrNone, info: '0};
      end
    endcase
  end : err_return

  assign error_o = err;

  // If below failed, revise err_swsequence error response info field.
  `ASSERT_INIT(ExpectedStSwCmdBits_A, $bits(st) == StateWidth && $bits(sw_cmd_i) == 6)

  // If failed, revise err_modestrength error info field.
  `ASSERT_INIT(ExpectedModeStrengthBits_A,
               $bits(cfg_mode_i) == 2 && $bits(cfg_strength_i) == 3)


  ///////////////////
  // State Machine //
  ///////////////////
  st_e st_gated_d;

  `PRIM_FLOP_SPARSE_FSM(u_state_regs, st_gated_d, st, st_e, StIdle)

  // ICEBOX(#14631): Move block_swcmd to PRIM_FLOP_SPARSE_FSM()
  //
  // It would be better to place this condition (block_swcmd) in `always_ff`
  // block to clearly indicate the clock gating condition. However, the
  // state machine uses the sparse encoding scheme and macro. It prevents any
  // latch enable signals.
  assign st_gated_d = (block_swcmd) ? st : st_d ;

  always_comb begin : next_state
    st_d = st;

    unique case (st)
      StIdle: begin
        if (!app_active_i && sw_cmd_i == CmdStart) begin
          // Proceed to the next state only when the SW issues the Start
          // command in a valid period.
          st_d = StMsgFeed;
        end else if (!app_active_i && sw_cmd_i == CmdStateWrite) begin
          // SW claims the block to write a saved Keccak state back.
          st_d = StStateWrite;
        end
      end

      StStateWrite: begin
        if (sw_cmd_i == CmdContinue) begin
          // The context is restored, resume absorbing the message.
          st_d = StMsgFeed;
        end else if (sw_cmd_i == CmdDone) begin
          // SW gives the block back without resuming a context.
          st_d = StIdle;
        end
      end

      StMsgFeed: begin
        if (sw_cmd_i inside {CmdProcess, CmdStop}) begin
          st_d = StProcessing;
        end
      end

      StProcessing: begin
        if (prim_mubi_pkg::mubi4_test_true_strict(sha3_absorbed_i)) begin
          st_d = StAbsorbed;
        end else if (prim_mubi_pkg::mubi4_test_true_strict(sha3_stopped_i)) begin
          st_d = StStopped;
        end
      end

      StAbsorbed: begin
        if (sw_cmd_i == CmdManualRun) begin
          st_d = StSqueezing;
        end else if (sw_cmd_i == CmdDone) begin
          st_d = StIdle;
        end
      end

      StStopped: begin
        if (sw_cmd_i == CmdDone) begin
          st_d = StIdle;
        end
      end

      StSqueezing: begin
        if (keccak_done_i) begin
          st_d = StAbsorbed;
        end
      end

      StTerminalError: begin
        // this state is terminal
        st_d = st;
      end

      default: begin
        // this state is terminal
        st_d = StTerminalError;
      end
    endcase

    // SEC_CM: FSM.GLOBAL_ESC, FSM.LOCAL_ESC
    // Unconditionally jump into the terminal error state
    // if the life cycle controller triggers an escalation.
    if (lc_ctrl_pkg::lc_tx_test_true_loose(lc_escalate_en_i)) begin
      st_d = StTerminalError;
    end

    if (st_d != StTerminalError &&
        prim_mubi_pkg::mubi4_test_true_strict(clear_after_error_i)) begin
      st_d = StIdle;
    end
  end : next_state
  `ASSERT_KNOWN(StKnown_A, st)

endmodule : kmac_errchk
