// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package otp_ctrl_pkg;

  /////////////////////////////////
  // Typedefs for OTP Scrambling //
  /////////////////////////////////

  parameter int PresentKeySize    = 128;
  parameter int PresentBlockSize  = 64;
  parameter int PresentDigestSize = 64;

  parameter int NumPresentRounds = 31;
  parameter int NumDigestRounds  = 4;

  // global netlist constants for OTP scrambling
  // from random.org
  parameter logic [PresentKeySize-1:0]   OtpEncKey      = 128'h047288e1a65c839dae610bbbdf8c4525;
  // TODO: the inverse key can be computed at compile time using the key schedule function
  parameter logic [PresentKeySize-1:0]   OtpDecKey      = 128'hb101e34ba8665f3b785d80927730bdc1;
  parameter logic [PresentKeySize-1:0]   OtpDigestConst = 128'hbad54428a1b587434e1dfdda898a1624;
  parameter logic [PresentBlockSize-1:0] OtpDigestIV    =  64'h43862458b34a5942;

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

  typedef struct packed {
    logic                            lc_state_valid;
    lifecycle_pkg::lc_value_e [5:0]  lc_state;
    logic                     [7:0]  id_state;
    logic                     [7:0]  test_state_cnt;
    logic                     [31:0] test_unlock_token;
    logic                     [31:0] test_exit_token;
    logic                     [63:0] rma_unlock_token;
    logic                     [7:0]  test_unlock_cnt;
    logic                     [7:0]  test_exit_cnt;
    logic                     [7:0]  rma_unlock_cnt;
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

  parameter lc_otp_program_req_t LC_OTP_PROGRAM_REQ_DEFAULT = '{
    update: '0,
    command: '0
  };

  typedef struct packed {
    logic  done;
  } lc_otp_program_rsp_t;

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

  // TODO: this is not final. we still need to figure out
  // how and where key derivation for SRAM should happen.
  typedef struct packed {
    logic valid;
    logic [FlashKeyWidth-1:0] key;
    logic [64-1:0]            nonce;
  } ram_main_key_t;

  typedef struct packed {
    logic valid;
    logic [FlashKeyWidth-1:0] key;
    logic [64-1:0]            nonce;
  } ram_ret_aon_key_t;

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
