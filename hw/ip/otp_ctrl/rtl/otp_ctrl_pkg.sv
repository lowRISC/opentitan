// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package otp_ctrl_pkg;

  /////////////////////////////////
  // Typedefs for OTP Scrambling //
  /////////////////////////////////

  parameter int PresentKeySize = 128;
  parameter int PresentBlockSize = 64;
  parameter int PresentDigestSize = 64;

  parameter int NumPresentRounds = 31;
  parameter int NumDigestRounds = 4;

  // global netlist constants for OTP scrambling
  // from random.org
  parameter logic [PresentKeySize-1:0] OtpEncKey = 128'h047288e1a65c839dae610bbbdf8c4525;
  // TODO: the inverse key can be computed at compile time using the key schedule function
  parameter logic [PresentKeySize-1:0] OtpDecKey = 128'hb101e34ba8665f3b785d80927730bdc1;
  parameter logic [PresentKeySize-1:0] OtpDigestConst = 128'hbad54428a1b587434e1dfdda898a1624;
  parameter logic [PresentBlockSize-1:0] OtpDigestIV = 64'h43862458b34a5942;

  typedef enum logic [2:0] {
    Decrypt,
    Encrypt,
    LoadHigh,
    LoadLow,
    DigestFirst,
    DigestUpdate,
    DigestFinalize
  } otp_scrmbl_cmd_e;

  ///////////////////////////////
  // Typedefs for LC Interface //
  ///////////////////////////////

  parameter int NumAlerts = 2;
  parameter logic [NumAlerts-1:0] AlertAsyncOn = NumAlerts'(1'b0);

  ///////////////////////////////
  // Typedefs for LC Interface //
  ///////////////////////////////

  // TODO: move to lc_ctrl_pkg
  typedef enum logic [7:0] {
    Value0 = 8'h00,
    Value1 = 8'h6D,
    Value2 = 8'h94,
    ValueF = 8'hFF
  } lc_value_e;

  // TODO: move to lc_ctrl_pkg
  typedef enum logic [47:0] {
    //                GRP5    GRP4    GRP3    GRP2    GRP1    GRP0
    LcStateRaw = {6{Value0}},
    LcStateTest = {Value0, Value0, Value0, Value0, Value0, Value1},
    LcStateDev = {Value0, Value0, Value2, Value2, Value1, Value1},
    LcStateProd = {Value0, Value0, Value2, Value1, Value2, Value1},
    LcStateProdEnd = {Value0, Value0, Value1, Value2, Value2, Value1},
    LcStateRma = {Value1, Value1, Value2, ValueF, ValueF, Value1},
    LcStateScrap = {6{ValueF}}
  } lc_state_e;

  typedef struct packed {
    logic lc_state_valid;
    lc_value_e [5:0] lc_state;
    logic [7:0] id_state;
    logic [7:0] test_state_cnt;
    logic [31:0] test_unlock_token;
    logic [31:0] test_exit_token;
    logic [63:0] rma_unlock_token;
    logic [7:0] test_unlock_cnt;
    logic [7:0] test_exit_cnt;
    logic [7:0] rma_unlock_cnt;
    // this must be incremented upon each state change
    // also, each invalid otp_program_cmd_e command will increment
    // this counter.
    logic [15:0] transition_cnt;
  } otp_lc_data_t;  // broadcast

  // TODO: this should have maximum Hamming distance encoding
  typedef enum logic [15:0] {
    // state transitions
    CmdGoToTestState = 16'h0001,
    CmdGoToDevState = 16'h0002,
    CmdGoToProdState = 16'h0003,
    CmdGoToProdEndState = 16'h0004,
    CmdGoToRmaState = 16'h0005,
    CmdGoToScrapState = 16'h0006,
    // counters
    CmdIncrTestStateCnt = 16'h0007,
    CmdIncrTestUnlockCnt = 16'h0008,
    CmdIncrRmaUnlockCnt = 16'h0009,
    CmdIncrTransitionCnt = 16'h000A
  } otp_program_cmd_e;

  typedef struct packed {
    logic update;
    otp_program_cmd_e command;
  } lc_otp_program_req_t;

  typedef struct packed {logic done;} lc_otp_program_rsp_t;

  // TODO: move this to the LC ctrl package
  typedef enum logic [2:0] {
    On = 3'b101,
    Off = 3'b000
  } lc_tx_e;

  // TODO: move this to the LC ctrl package
  typedef struct packed {lc_tx_e state;} lc_tx_t;


  ////////////////////////////////
  // Typedefs for Key Broadcast //
  ////////////////////////////////

  parameter int KeyMgrKeyWidth = 256;
  parameter int FlashKeyWidth = 128;

  typedef struct packed {
    logic valid;
    logic [KeyMgrKeyWidth-1:0] key_share0;
    logic [KeyMgrKeyWidth-1:0] key_share1;
  } keymgr_key_t;

  typedef struct packed {
    logic valid;
    logic [FlashKeyWidth-1:0] addr_key;
    logic [FlashKeyWidth-1:0] data_key;
  } flash_key_t;


  ////////////////////////////////
  // Power/Reset Ctrl Interface //
  ////////////////////////////////

  typedef struct packed {logic init;} pwr_otp_init_req_t;

  typedef struct packed {logic done;} pwr_otp_init_rsp_t;

  typedef enum logic [1:0] {
    Idle = 2'b00,
    Reading = 2'b01,
    Writing = 2'b10
  } otp_pwr_state_e;

  typedef struct packed {otp_pwr_state_e state;} otp_pwr_state_t;

endpackage : otp_ctrl_pkg


