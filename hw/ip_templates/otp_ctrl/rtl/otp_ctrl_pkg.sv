// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This package can be imported by generic IPs:
// - It does not import otp_ctrl_reg_pkg, which is generated and top-specific.

package otp_ctrl_pkg;

  ////////////////////////
  // General Parameters //
  ////////////////////////

  // Number of vendor-specific test CSR bits coming from and going to
  // the life cycle TAP registers.
  parameter int OtpTestCtrlWidth   = 32;
  parameter int OtpTestStatusWidth = 32;
  parameter int OtpTestVectWidth   = 8;

  parameter int DeviceIdWidth = 256;
  typedef logic [DeviceIdWidth-1:0] otp_device_id_t;

  parameter int ManufStateWidth = 256;
  typedef logic [ManufStateWidth-1:0] otp_manuf_state_t;

  // OTP-macro specific
  parameter int OtpPwrSeqWidth   = 2;

  /////////////////////////////////
  // Typedefs for OTP Scrambling //
  /////////////////////////////////

  parameter int ScrmblKeyWidth   = 128;
  parameter int ScrmblBlockWidth = 64;

  ///////////////////////////////
  // Typedefs for LC Interface //
  ///////////////////////////////

  // The tokens below are all hash post-images
  typedef struct packed {
    logic                            valid;
    logic                            error;
    // Use lc_state_t and lc_cnt_t here as very wide enumerations ( > 64 bits )
    // are not supported for virtual interfaces by Excelium yet
    // https://github.com/lowRISC/opentitan/issues/8884 (Cadence issue: cds_46570160)
    // The enumeration types lc_state_e and lc_cnt_e are still ok in other circumstances
    lc_ctrl_state_pkg::lc_state_t    state;
    lc_ctrl_state_pkg::lc_cnt_t      count;
    // This is set to "On" if the partition containing the
    // root secrets have been locked. In that case, the device
    // is considered "personalized".
    lc_ctrl_pkg::lc_tx_t             secrets_valid;
    // This is set to "On" if the partition containing the
    // test tokens has been locked.
    lc_ctrl_pkg::lc_tx_t             test_tokens_valid;
    lc_ctrl_state_pkg::lc_token_t    test_unlock_token;
    lc_ctrl_state_pkg::lc_token_t    test_exit_token;
    // This is set to "On" if the partition containing the
    // rma token has been locked.
    lc_ctrl_pkg::lc_tx_t             rma_token_valid;
    lc_ctrl_state_pkg::lc_token_t    rma_token;
  } otp_lc_data_t;

  // Default for dangling connection.
  // Note that we put the life cycle into
  // TEST_UNLOCKED0 by default such that top levels without
  // the OTP controller can still function.
  parameter otp_lc_data_t OTP_LC_DATA_DEFAULT = '{
    valid: 1'b1,
    error: 1'b0,
    state: lc_ctrl_state_pkg::LcStTestUnlocked0,
    count: lc_ctrl_state_pkg::LcCnt1,
    secrets_valid: lc_ctrl_pkg::Off,
    test_tokens_valid: lc_ctrl_pkg::Off,
    test_unlock_token: '0,
    test_exit_token: '0,
    rma_token_valid: lc_ctrl_pkg::Off,
    rma_token: '0
  };

  typedef struct packed {
    logic req;
    lc_ctrl_state_pkg::lc_state_e state;
    lc_ctrl_state_pkg::lc_cnt_e   count;
  } lc_otp_program_req_t;

  typedef struct packed {
    logic err;
    logic ack;
  } lc_otp_program_rsp_t;

  typedef struct packed {
    logic [OtpTestCtrlWidth-1:0] ctrl;
  } lc_otp_vendor_test_req_t;

  typedef struct packed {
    logic [OtpTestStatusWidth-1:0] status;
  } lc_otp_vendor_test_rsp_t;

  ////////////////////////////////
  // Typedefs for Key Broadcast //
  ////////////////////////////////

  parameter int FlashKeySeedWidth = 256;
  parameter int SramKeySeedWidth  = 128;
  parameter int KeyMgrKeyWidth    = 256;
  parameter int FlashKeyWidth     = 128;
  parameter int SramKeyWidth      = 128;
  parameter int SramNonceWidth    = 128;
  parameter int OtbnKeyWidth      = 128;
  parameter int OtbnNonceWidth    = 64;

  typedef logic [SramKeyWidth-1:0]   sram_key_t;
  typedef logic [SramNonceWidth-1:0] sram_nonce_t;
  typedef logic [OtbnKeyWidth-1:0]   otbn_key_t;
  typedef logic [OtbnNonceWidth-1:0] otbn_nonce_t;

  localparam int OtbnNonceSel  = OtbnNonceWidth / ScrmblBlockWidth;
  localparam int FlashNonceSel = FlashKeyWidth / ScrmblBlockWidth;
  localparam int SramNonceSel  = SramNonceWidth / ScrmblBlockWidth;

  // Get maximum nonce width
  localparam int NumNonceChunks =
    (OtbnNonceWidth > FlashKeyWidth) ?
    ((OtbnNonceWidth > SramNonceSel) ? OtbnNonceSel : SramNonceSel) :
    ((FlashKeyWidth > SramNonceSel)  ? FlashNonceSel  : SramNonceSel);

  typedef struct packed {
    logic [KeyMgrKeyWidth-1:0] creator_root_key_share0;
    logic creator_root_key_share0_valid;
    logic [KeyMgrKeyWidth-1:0] creator_root_key_share1;
    logic creator_root_key_share1_valid;
    logic [KeyMgrKeyWidth-1:0] creator_seed;
    logic creator_seed_valid;
    logic [KeyMgrKeyWidth-1:0] owner_seed;
    logic owner_seed_valid;
  } otp_keymgr_key_t;

  parameter otp_keymgr_key_t OTP_KEYMGR_KEY_DEFAULT = '{
    creator_root_key_share0: 256'hefb7ea7ee90093cf4affd9aaa2d6c0ec446cfdf5f2d5a0bfd7e2d93edc63a102,
    creator_root_key_share0_valid: 1'b1,
    creator_root_key_share1: 256'h56d24a00181de99e0f690b447a8dde2a1ffb8bc306707107aa6e2410f15cfc37,
    creator_root_key_share1_valid: 1'b1,
    creator_seed: 256'hc7c50b38655cc87f821e5b07fed85d2c07e222a9e00bef308b3eccba0ba406fa,
    creator_seed_valid: 1'b1,
    owner_seed: 256'hf5052c0f14782d8b066be9f49c0b2000d3643ff3723ea7db972f69cd3e2e3e68,
    owner_seed_valid: 1'b1
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
    logic data_ack;                    // Ack for data key.
    logic addr_ack;                    // Ack for address key.
    logic [FlashKeyWidth-1:0] key;     // 128bit static scrambling key.
    logic [FlashKeyWidth-1:0] rand_key;
    logic seed_valid;                  // Set to 1 if the key seed has been provisioned and is
                                       // valid.
  } flash_otp_key_rsp_t;

  // Default for dangling connection
  parameter flash_otp_key_rsp_t FLASH_OTP_KEY_RSP_DEFAULT = '{
    data_ack: 1'b1,
    addr_ack: 1'b1,
    key: '0,
    rand_key: '0,
    seed_valid: 1'b1
  };

  typedef struct packed {
    logic        ack;        // Ack for key.
    sram_key_t   key;        // 128bit ephemeral scrambling key.
    sram_nonce_t nonce;      // 128bit nonce.
    logic        seed_valid; // Set to 1 if the key seed has been provisioned and is valid.
  } sram_otp_key_rsp_t;

  // Default for dangling connection
  parameter sram_otp_key_rsp_t SRAM_OTP_KEY_RSP_DEFAULT = '{
    ack: 1'b1,
    key: '0,
    nonce: '0,
    seed_valid: 1'b1
  };

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

endpackage : otp_ctrl_pkg
