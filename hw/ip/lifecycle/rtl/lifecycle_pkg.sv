// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//


package lifecycle_pkg;

  typedef enum logic [7:0] {
    Value0 = 8'h 00,
    Value1 = 8'h 6D,
    Value2 = 8'h 94,
    ValueF = 8'h FF
  } lc_value_e;

  //typedef enum lc_value_e [5:0] {
  localparam int LcStateGroups = 6;
  localparam int LcStateWidth = $bits(lc_value_e) * LcStateGroups;
  typedef enum logic [LcStateWidth-1:0] {
    //                GRP5    GRP4    GRP3    GRP2    GRP1    GRP0
    LcStateRaw     = {6{Value0}},
    LcStateTest    = {Value0, Value0, Value0, Value0, Value0, Value1},
    LcStateDev     = {Value0, Value0, Value2, Value2, Value1, Value1},
    LcStateProd    = {Value0, Value0, Value2, Value1, Value2, Value1},
    LcStateProdEnd = {Value0, Value0, Value1, Value2, Value2, Value1},
    LcStateRma     = {Value1, Value1, Value2, ValueF, ValueF, Value1},
    LcStateScrap   = {6{ValueF}}
  } lc_state_e;

  localparam int LcRstGroups = 3;
  localparam int LcRstWidth = $bits(lc_value_e) * LcRstGroups;
  typedef enum logic [LcRstWidth-1:0] {
    StReset        = {Value0, Value0, Value0}, // idle 0 at reset, move to next
    StInitWait     = {Value0, Value0, Value1}, // make idle 1 and wait lc_init
    StOtpReq       = {Value0, Value1, Value1}, // wait otp_data.lc_state_valid
    StLcCheck      = {Value0, Value1, Value0}, // check value is correct
    StStrapReq     = {Value1, Value1, Value0}, // send req to pinmux to strap based on state
    StStrapCheck   = {Value1, Value1, Value1},
    StLcBroadcast  = {Value1, Value0, Value1}, // valid output to rest of IPs
    StScrap        = {Value1, Value0, Value0}  // Virtual Scrap state if life cycle check failed
  } rst_state_e;

  localparam int LcOtpGroups = 2;
  localparam int LcOtpWidth = $bits(lc_value_e) * LcOtpGroups;
  typedef enum logic [LcOtpWidth-1:0] {
    StIdle       = {Value0, Value0},
    StOtpProgram = {Value0, Value1}, // Sending program req w/ command
    StOtpDone    = {Value1, Value1}  // Make Lifecycle waiting reset
  } otp_state_e;

  typedef enum logic [2:0] {
    On  = 3'b101,
    Off = 3'b000
  } lc_tx_e;

  typedef struct packed {
    lc_tx_e state;
  } lc_tx_t;

  parameter lc_tx_t LC_TX_DEFAULT = '{state: Off};

  // from otp_ctrl_pkg
  //typedef enum logic [15:0] {
  //  // state transitions
  //  CmdGoToTestState      = 16'h0001,
  //  CmdGoToDevState       = 16'h0002,
  //  CmdGoToProdState      = 16'h0003,
  //  CmdGoToProdEndState   = 16'h0004,
  //  CmdGoToRmaState       = 16'h0005,
  //  CmdGoToScrapState     = 16'h0006,
  //  // counters
  //  CmdIncrTestStateCnt   = 16'h0007,
  //  CmdIncrTestUnlockCnt  = 16'h0008,
  //  CmdIncrRmaUnlockCnt   = 16'h0009,
  //  CmdIncrTransitionCnt  = 16'h000A
  //} otp_program_cmd_e;

  //typedef struct packed {
  //  logic             update;
  //  otp_program_cmd_e command;
  //} lc_otp_program_req_t;

  //typedef struct packed {
  //  logic  done;
  //} lc_otp_program_rsp_t;

  //typedef struct packed {
  //  logic             lc_state_valid;
  //  lc_value_e [5:0]  lc_state;
  //  logic      [7:0]  id_state;
  //  logic      [7:0]  test_state_cnt;
  //  logic      [31:0] test_unlock_token;
  //  logic      [31:0] test_exit_token;
  //  logic      [63:0] rma_unlock_token;
  //  logic      [7:0]  test_unlock_cnt;
  //  logic      [7:0]  test_exit_cnt;
  //  logic      [7:0]  rma_unlock_cnt;
  //  // this must be incremented upon each state change
  //  // also, each invalid otp_program_cmd_e command will increment
  //  // this counter.
  //  logic      [15:0] transition_cnt;
  //} otp_lc_data_t;  // broadcast

endpackage : lifecycle_pkg

