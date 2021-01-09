// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package otp_ctrl_pkg;

  import prim_util_pkg::vbits;
  import otp_ctrl_reg_pkg::*;

  ////////////////////////
  // General Parameters //
  ////////////////////////

  // Width of entropy input
  parameter int EdnDataWidth = 64;

  parameter int NumPartWidth = vbits(NumPart);

  parameter int SwWindowAddrWidth = vbits(NumSwCfgWindowWords);

  // Redundantly encoded and complementary values are used to for signalling to the partition
  // controller FSMs and the DAI whether a partition is locked or not. Any other value than
  // "Unlocked" is interpreted as "Locked" in those FSMs.
  typedef enum logic [7:0] {
    Unlocked = 8'h5A,
    Locked   = 8'hA5
  } access_e;

  // Partition access type
  typedef struct packed {
    access_e read_lock;
    access_e write_lock;
  } part_access_t;

  parameter int DaiCmdWidth = 3;
  typedef enum logic [DaiCmdWidth-1:0] {
    DaiRead   = 3'b001,
    DaiWrite  = 3'b010,
    DaiDigest = 3'b100
  } dai_cmd_e;

  //////////////////////////////////////
  // Typedefs for OTP Macro Interface //
  //////////////////////////////////////

  // OTP-macro specific
  parameter int OtpWidth         = 16;
  parameter int OtpAddrWidth     = OtpByteAddrWidth - $clog2(OtpWidth/8);
  parameter int OtpDepth         = 2**OtpAddrWidth;
  parameter int OtpSizeWidth     = 2; // Allows to transfer up to 4 native OTP words at once.
  parameter int OtpErrWidth      = 3;
  parameter int OtpPwrSeqWidth   = 2;
  parameter int OtpIfWidth       = 2**OtpSizeWidth*OtpWidth;
  // Number of Byte address bits to cut off in order to get the native OTP word address.
  parameter int OtpAddrShift     = OtpByteAddrWidth - OtpAddrWidth;

  typedef enum logic [OtpErrWidth-1:0] {
    NoError              = 3'h0,
    MacroError           = 3'h1,
    MacroEccCorrError    = 3'h2,
    MacroEccUncorrError  = 3'h3,
    MacroWriteBlankError = 3'h4,
    AccessError          = 3'h5,
    CheckFailError       = 3'h6,
    FsmStateError        = 3'h7
  } otp_err_e;

  /////////////////////////////////
  // Typedefs for OTP Scrambling //
  /////////////////////////////////

  parameter int ScrmblKeyWidth   = 128;
  parameter int ScrmblBlockWidth = 64;

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

  ///////////////////////////////
  // Typedefs for LC Interface //
  ///////////////////////////////

  typedef struct packed {
    logic                      valid;
    logic                      error;
    lc_ctrl_pkg::lc_state_e    state;
    lc_ctrl_pkg::lc_cnt_e      count;
    // These are all hash post-images
    lc_ctrl_pkg::lc_token_t    test_unlock_token;
    lc_ctrl_pkg::lc_token_t    test_exit_token;
    lc_ctrl_pkg::lc_token_t    rma_token;
    lc_ctrl_pkg::lc_id_state_e id_state;
  } otp_lc_data_t;

  // Default for dangling connection
  parameter otp_lc_data_t OTP_LC_DATA_DEFAULT = '{
    valid: 1'b1,
    error: 1'b0,
    state: lc_ctrl_pkg::LcStRaw,
    count: lc_ctrl_pkg::LcCntRaw,
    test_unlock_token: '0,
    test_exit_token: '0,
    rma_token: '0,
    id_state: lc_ctrl_pkg::LcIdBlank
  };

  typedef struct packed {
    logic req;
    lc_ctrl_pkg::lc_state_e state;
    lc_ctrl_pkg::lc_cnt_e   count;
  } lc_otp_program_req_t;

  typedef struct packed {
    logic err;
    logic ack;
  } lc_otp_program_rsp_t;

  // RAW unlock token hashing request.
  typedef struct packed {
    logic req;
    lc_ctrl_pkg::lc_token_t token_input;
  } lc_otp_token_req_t;

  typedef struct packed {
    logic ack;
    lc_ctrl_pkg::lc_token_t hashed_token;
  } lc_otp_token_rsp_t;

  ////////////////////////////////
  // Typedefs for Key Broadcast //
  ////////////////////////////////

  parameter int FlashKeySeedWidth = 256;
  parameter int SramKeySeedWidth  = 128;
  parameter int KeyMgrKeyWidth   = 256;
  parameter int FlashKeyWidth    = 128;
  parameter int SramKeyWidth     = 128;
  parameter int SramNonceWidth   = 64;
  parameter int OtbnKeyWidth     = 128;
  parameter int OtbnNonceWidth   = 256;

  typedef logic [SramKeyWidth-1:0]   sram_key_t;
  typedef logic [SramNonceWidth-1:0] sram_nonce_t;
  typedef logic [OtbnKeyWidth-1:0]   otbn_key_t;
  typedef logic [OtbnNonceWidth-1:0] otbn_nonce_t;

  typedef struct packed {
    logic valid;
    logic [KeyMgrKeyWidth-1:0] key_share0;
    logic [KeyMgrKeyWidth-1:0] key_share1;
  } otp_keymgr_key_t;

  parameter otp_keymgr_key_t OTP_KEYMGR_KEY_DEFAULT = '{
    valid: 1'b1,
    key_share0: 256'hefb7ea7ee90093cf4affd9aaa2d6c0ec446cfdf5f2d5a0bfd7e2d93edc63a102,
    key_share1: 256'h56d24a00181de99e0f690b447a8dde2a1ffb8bc306707107aa6e2410f15cfc37
  };

  typedef struct packed {
    logic data_req; // Requests static key for data scrambling.
    logic addr_req; // Requests static key for address scrambling.
  } flash_otp_key_req_t;

  typedef struct packed {
    logic req; // Requests ephemeral scrambling key and nonce.
  } sram_otp_key_req_t;

  typedef struct packed {
    logic req; // Requests ephemeral scrambling key and nonce.
  } otbn_otp_key_req_t;

  typedef struct packed {
    logic data_ack;                // Ack for data key.
    logic addr_ack;                // Ack for address key.
    logic [FlashKeyWidth-1:0] key; // 128bit static scrambling key.
    logic seed_valid;              // Set to 1 if the key seed has been provisioned and is valid.
  } flash_otp_key_rsp_t;

  // Default for dangling connection
  parameter flash_otp_key_rsp_t FLASH_OTP_KEY_RSP_DEFAULT = '{
    data_ack: 1'b1,
    addr_ack: 1'b1,
    key: '0,
    seed_valid: 1'b1
  };

  typedef struct packed {
    logic        ack;         // Ack for key.
    sram_key_t   key;        // 128bit ephemeral scrambling key.
    sram_nonce_t nonce;      // 64bit nonce.
    logic        seed_valid; // Set to 1 if the key seed has been provisioned and is valid.
  } sram_otp_key_rsp_t;

  typedef struct packed {
    logic        ack;        // Ack for key.
    otbn_key_t   key;        // 128bit ephemeral scrambling key.
    otbn_nonce_t nonce;      // 256bit nonce.
    logic        seed_valid; // Set to 1 if the key seed has been provisioned and is valid.
  } otbn_otp_key_rsp_t;

  ////////////////////////////////
  // Power/Reset Ctrl Interface //
  ////////////////////////////////

  typedef struct packed {
    logic init;
  } pwr_otp_init_req_t;

  typedef struct packed {
    logic done;
  } pwr_otp_init_rsp_t;

  typedef struct packed {
    logic idle;
  } otp_pwr_state_t;


  ///////////////////
  // AST Interface //
  ///////////////////

  typedef struct packed {
    logic [OtpPwrSeqWidth-1:0] pwr_seq;
  } otp_ast_req_t;

  typedef struct packed {
    logic [OtpPwrSeqWidth-1:0] pwr_seq_h;
  } otp_ast_rsp_t;

  ///////////////////////////////////////////
  // Defaults for random netlist constants //
  ///////////////////////////////////////////

  // These LFSR parameters have been generated with
  // $ util/design/gen-lfsr-seed.py --width 40 --seed 4247488366
  localparam int LfsrWidth = 40;
  typedef logic [LfsrWidth-1:0]                        lfsr_seed_t;
  typedef logic [LfsrWidth-1:0][$clog2(LfsrWidth)-1:0] lfsr_perm_t;
  localparam lfsr_seed_t RndCnstLfsrSeedDefault = 40'h453d28ea98;
  localparam lfsr_perm_t RndCnstLfsrPermDefault =
      240'h4235171482c225f79289b32181a0163a760355d3447063d16661e44c12a5;

endpackage : otp_ctrl_pkg
