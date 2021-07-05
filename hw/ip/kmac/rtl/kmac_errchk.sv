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

module kmac_errchk
  import kmac_pkg::*;
  import sha3_pkg::sha3_mode_e;
  import sha3_pkg::keccak_strength_e;
(
  input clk_i,
  input rst_ni,

  // Configurations
  input sha3_mode_e       cfg_mode_i,
  input keccak_strength_e cfg_strength_i,

  input        kmac_en_i,
  input [47:0] cfg_prefix_6B_i, // first 6B of PREFIX

  // SW commands
  input kmac_cmd_e sw_cmd_i,

  // Status from KMAC_APP
  input app_active_i,

  // Status from SHA3 core
  input sha3_absorbed_i,
  input keccak_done_i,

  output err_t error_o
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
  typedef enum logic [2:0] {
    StIdle,
    StMsgFeed,
    StProcessing,
    StAbsorbed,
    StSqueezing
  } st_e;
  st_e st, st_d;

  /////////////
  // Signals //
  /////////////

  // `err_swsequence` occurs when SW issues wrong command
  logic err_swsequence;

  // `err_modestrength` occcurs when Mode & Strength combinations are not
  // allowed. This error does not block the hashing operation.
  logic err_modestrength;

  // `err_prefix` occurs when the first 6B of !!PREFIX is not
  // `encode_string("KMAC")` and kmac is enabled. This error does not block the
  // KMAC operation.
  logic err_prefix;

  ///////////////////
  // Error Checker //
  ///////////////////

  // SW sequence Error
  // info field: Current state, Received command
  always_comb begin
    err_swsequence = 1'b 0;

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

      default: begin
        err_swsequence = 1'b 0;
      end
    endcase
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
                        8'h0,
                        {1'b0, st, sw_cmd_i}
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

      default: begin
        err = '{valid: 1'b0, code: ErrNone, info: '0};
      end
    endcase
  end : err_return

  assign error_o = err;

  // If below failed, revise err_swsequence error response info field.
  `ASSERT_INIT(ExpectedStSwCmdBits_A, $bits(st) == 3 && $bits(sw_cmd_i) == 4)

  // If failed, revise err_modestrength error info field.
  `ASSERT_INIT(ExpectedModeStrengthBits_A,
               $bits(cfg_mode_i) == 2 && $bits(cfg_strength_i) == 3)


  ///////////////////
  // State Machine //
  ///////////////////
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      st <= StIdle;
    end else begin
      st <= st_d;
    end
  end

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
        if (sha3_absorbed_i) begin
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

      default: begin
        st_d = StIdle;
      end
    endcase
  end : next_state
  `ASSERT_KNOWN(StKnown_A, st)

endmodule : kmac_errchk
