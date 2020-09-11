// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package otp_ctrl_pkg;

  import prim_util_pkg::vbits;

  //////////////////////////////////////
  // Typedefs for OTP Macro Interface //
  //////////////////////////////////////

  // OTP-macro specific
  parameter int OtpWidth         = 16;
  parameter int OtpDepth         = 1024;
  parameter int OtpCmdWidth      = 2;
  parameter int OtpSizeWidth     = 2; // Allows to transfer up to 4 native OTP words at once.
  parameter int OtpErrWidth      = 4;
  parameter int OtpAddrWidth     = vbits(OtpDepth);
  parameter int OtpByteAddrWidth = vbits(OtpWidth/8 * OtpDepth);
  parameter int OtpIfWidth       = 2**OtpSizeWidth*OtpWidth;
  // Number of Byte address bits to cut off in order to get the native OTP word address.
  parameter int OtpAddrShift     = OtpByteAddrWidth - OtpAddrWidth;

  typedef enum logic [OtpCmdWidth-1:0] {
    OtpRead  = 2'b00,
    OtpWrite = 2'b01,
    OtpInit  = 2'b11
  } prim_otp_cmd_e;

  typedef enum logic [OtpErrWidth-1:0] {
    None                 = 4'h0,
    OtpCmdInvErr         = 4'h1,
    OtpSizeInvErr        = 4'h2,
    OtpInitErr           = 4'h3,
    OtpReadErrEccCorr    = 4'h4,
    OtpReadErrEccUncorr  = 4'h5,
    OtpReadErrOther      = 4'h6,
    OtpWriteErrNotBlank  = 4'h7,
    OtpWriteErrOther     = 4'h8,
    ParityErr            = 4'h9,
    IntegErr             = 4'hA,
    CnstyErr             = 4'hB,
    FsmErr               = 4'hC,
    CmdInvErr            = 4'hD,
    AccessErr            = 4'hE
    // TODO: populate with error codes
  } otp_err_e;

  /////////////////////////////////
  // Typedefs for OTP Scrambling //
  /////////////////////////////////

  parameter int ScrmblKeyWidth   = 128;
  parameter int ScrmblBlockWidth = 64;
  parameter int DigestBlockWidth = 64;

  parameter int NumPresentRounds = 31;
  parameter int ScrmblBlockHalfWords = ScrmblBlockWidth / OtpWidth;

  typedef enum logic [2:0] {
    Decrypt,
    Encrypt,
    LoadShadow,
    Digest,
    DigestInit,
    DigestFinalize
  } otp_scrmbl_cmd_e;

  // NOTE: THESE CONSTANTS HAVE TO BE REPLACED BEFORE TAPING OUT.
  // TODO(#2229): need to put mechanism in place to manage these constants.
  // Global netlist constants for OTP scrambling and digest calculation.
  // Sample values below have been obtained from random.org
  parameter int NumScrmblKeys = 3;
  parameter int NumDigestSets = 5;
  parameter int ConstSelWidth = (NumScrmblKeys > NumDigestSets) ?
                               vbits(NumScrmblKeys) :
                               vbits(NumDigestSets);
  parameter logic [ScrmblKeyWidth-1:0] OtpKey [NumScrmblKeys] = '{
    128'h047288e1a65c839dae610bbbdf8c4525,
    128'h38fe59a71a91a65636573a6513784e3b,
    128'h4f48dcc45ace0770e9135bda73e56344
  };
  // Note: digest set 0 is used for computing the partition digests. Constants at
  // higher indices are used to compute the scrambling keys.
  parameter logic [ScrmblKeyWidth-1:0] OtpDigestConst [NumDigestSets] = '{
    128'h9d40106e2dc2346ec96d61f0cc5295c7,
    128'hafed2aa5c3284c01d71103edab1d8953,
    128'h8a14fe0c08f8a3a190dd32c05f208474,
    128'h9e6fac4ba15a3bce29d05a3e9e2d0846,
    128'h3a0c6051392e00ef24073627319555b8
  };
  parameter logic [ScrmblBlockWidth-1:0] OtpDigestIV [NumDigestSets] = '{
    64'ha5af72c1b813aec4,
    64'h5d7aacd1db316407,
    64'hd0ec83b7fe6ae2ae,
    64'hc2993a0ea64e312d,
    64'h899aac2ab7d91479
  };

  typedef enum logic [ConstSelWidth-1:0] {
    StandardMode,
    ChainedMode
  } otp_digest_mode_e;

  ///////////////////////////////
  // Typedefs for LC Interface //
  ///////////////////////////////

  // TODO: move to lc_ctrl_pkg
  typedef enum logic [7:0] {
    Value0 = 8'h 00,
    Value1 = 8'h 6D,
    Value2 = 8'h 94,
    ValueF = 8'h FF
  } lc_value_e;

  // TODO: move to lc_ctrl_pkg
  typedef enum logic [47:0] {
    //                GRP5    GRP4    GRP3    GRP2    GRP1    GRP0
    LcStateRaw     = {6{Value0}},
    LcStateTest    = {Value0, Value0, Value0, Value0, Value0, Value1},
    LcStateDev     = {Value0, Value0, Value2, Value2, Value1, Value1},
    LcStateProd    = {Value0, Value0, Value2, Value1, Value2, Value1},
    LcStateProdEnd = {Value0, Value0, Value1, Value2, Value2, Value1},
    LcStateRma     = {Value1, Value1, Value2, ValueF, ValueF, Value1},
    LcStateScrap   = {6{ValueF}}
  } lc_state_e;

  typedef struct packed {
    logic             lc_state_valid;
    lc_value_e [5:0]  lc_state;
    logic      [7:0]  id_state;
    logic      [7:0]  test_state_cnt;
    logic      [31:0] test_unlock_token;
    logic      [31:0] test_exit_token;
    logic      [63:0] rma_unlock_token;
    logic      [7:0]  test_unlock_cnt;
    logic      [7:0]  test_exit_cnt;
    logic      [7:0]  rma_unlock_cnt;
    // this must be incremented upon each state change
    // also, each invalid otp_program_cmd_e command will increment
    // this counter.
    logic      [15:0] transition_cnt;
  } otp_lc_data_t;  // broadcast

  // TODO: this should have maximum Hamming distance encoding
  typedef enum logic [15:0] {
    // state transitions
    CmdGoToTestState      = 16'h0001,
    CmdGoToDevState       = 16'h0002,
    CmdGoToProdState      = 16'h0003,
    CmdGoToProdEndState   = 16'h0004,
    CmdGoToRmaState       = 16'h0005,
    CmdGoToScrapState     = 16'h0006,
    // counters
    CmdIncrTestStateCnt   = 16'h0007,
    CmdIncrTestUnlockCnt  = 16'h0008,
    CmdIncrRmaUnlockCnt   = 16'h0009,
    CmdIncrTransitionCnt  = 16'h000A
  } otp_program_cmd_e;

  typedef struct packed {
    logic             update;
    otp_program_cmd_e command;
  } lc_otp_program_req_t;

  typedef struct packed {
    logic  done;
  } lc_otp_program_rsp_t;

  // TODO: move this to the LC ctrl package
  typedef enum logic [2:0] {
    On  = 3'b101,
    Off = 3'b000
  } lc_tx_e;

  // TODO: move this to the LC ctrl package
  typedef struct packed {
    lc_tx_e state;
  } lc_tx_t;


  ////////////////////////////////
  // Typedefs for Key Broadcast //
  ////////////////////////////////

  parameter int KeyMgrKeyWidth = 256;
  parameter int FlashKeyWidth  = 128;

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

  typedef struct packed {
    logic  init;
  } pwr_otp_init_req_t;

  typedef struct packed {
    logic  done;
  } pwr_otp_init_rsp_t;

  typedef enum logic [1:0] {
    Idle    = 2'b00,
    Reading = 2'b01,
    Writing = 2'b10
  } otp_pwr_state_e;

  typedef struct packed {
    otp_pwr_state_e  state;
  } otp_pwr_state_t;

endpackage : otp_ctrl_pkg


