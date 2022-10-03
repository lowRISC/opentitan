// Copyright lowRISC contributors.
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
// st := { Idle, MsgFeed, Processing, Absorbed, Squeeze}
//
// allowed := {
//   Idle :      { Start     },
//   MsgFeed:    { Process   },
//   Processing: { None      },
//   Absorbed:   { Run, Done },
//   Squeeze:    { None      }
// }
//
// ## SW Configuration Error
//
// `kmac_errchk` module checks if SW configured correct combinations of the
// configuration registers when the hashing operation begins.
//
// 1. Mode & Strength combinations
// 2. Kmac Prefix
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
  input [47:0] cfg_prefix_6B_i, // first 6B of PREFIX

  // If the signal below is set, errchk propagates the command to the rest of
  // the blocks even with err_modestrength.
  input        cfg_en_unsupported_modestrength_i,

  // Entropy Ready Status to check if SW initiated the hahs without entropy cfg
  input        entropy_ready_pulse_i,

  // SW commands: Only valid command is sent out to the rest of the modules
  input  kmac_cmd_e sw_cmd_i,
  output kmac_cmd_e sw_cmd_o,

  // Status from KMAC_APP
  input app_active_i,

  // Status from SHA3 core
  input prim_mubi_pkg::mubi4_t sha3_absorbed_i,
  input keccak_done_i,

  // Life cycle
  input  lc_ctrl_pkg::lc_tx_t lc_escalate_en_i,

  // Error processed indicator
  input err_processed_i,

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
  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 5 -n 6 \
  //      -s 2239170217 --language=sv
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
  // Minimum Hamming weight: 2
  // Maximum Hamming weight: 4
  //
  localparam int StateWidth = 6;
  typedef enum logic [StateWidth-1:0] {
    StIdle = 6'b001101,
    StMsgFeed = 6'b110001,
    StProcessing = 6'b010110,
    StAbsorbed = 6'b100010,
    StSqueezing = 6'b111100,
    StTerminalError = 6'b011011
  } st_e;
  st_e st, st_d;

  localparam int StateWidthL = 3;
  typedef enum logic [StateWidthL-1:0] {
    StIdleL,
    StMsgFeedL,
    StProcessingL,
    StAbsorbedL,
    StSqueezingL,
    StErrorL
  } st_logical_e;
  st_logical_e stL;


  /////////////
  // Signals //
  /////////////

  // `err_swsequence` occurs when SW issues wrong command
  logic err_swsequence;

  // `err_modestrength` occcurs when Mode & Strength combinations are not
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
        // Allow Start command only
        if (!(sw_cmd_i inside {CmdNone, CmdStart})) begin
          err_swsequence = 1'b 1;
        end
      end

      StMsgFeed: begin
        // Allow Process only
        if (!(sw_cmd_i inside {CmdNone, CmdProcess})) begin
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

  assign block_swcmd =  (err_swsequence)
                     || (err_modestrength
                         && !cfg_en_unsupported_modestrength_i)
                     || err_entropy_ready;

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

  end

  always_comb begin : recode_st
    unique case (st)
      StIdle       : stL = StIdleL;
      StMsgFeed    : stL = StMsgFeedL;
      StProcessing : stL = StProcessingL;
      StAbsorbed   : stL = StAbsorbedL;
      StSqueezing  : stL = StSqueezingL;
      default      : stL = StErrorL;
    endcase
  end : recode_st

  // Return error code
  err_t err;
  always_comb begin : err_return
    err = '{valid: 1'b0, code: ErrNone, info: '0};

    priority case (1'b 1)
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
  // statemachine uses the sparse encoding scheme and macro. It prevents any
  // latch enable signals.
  assign st_gated_d = (block_swcmd) ? st : st_d ;

  always_comb begin : next_state
    st_d = st;

    unique case (st)
      StIdle: begin
        if (!app_active_i && sw_cmd_i == CmdStart) begin
          // Proceed to the next state only when the SW issues the Start command
          // in a valid period.
          st_d = StMsgFeed;
        end
      end

      StMsgFeed: begin
        if (sw_cmd_i == CmdProcess) begin
          st_d = StProcessing;
        end
      end

      StProcessing: begin
        if (prim_mubi_pkg::mubi4_test_true_strict(sha3_absorbed_i)) begin
          st_d = StAbsorbed;
        end
      end

      StAbsorbed: begin
        if (sw_cmd_i == CmdManualRun) begin
          st_d = StSqueezing;
        end else if (sw_cmd_i == CmdDone) begin
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
    if (lc_escalate_en_i != lc_ctrl_pkg::Off) begin
      st_d = StTerminalError;
    end
  end : next_state
  `ASSERT_KNOWN(StKnown_A, st)

endmodule : kmac_errchk
