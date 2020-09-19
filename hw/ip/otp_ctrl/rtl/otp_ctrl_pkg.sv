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

  parameter int NumPart = 7;
  parameter int NumPartWidth = vbits(NumPart);
  // This defines the width of the check timers and LFSR
  parameter int TimerWidth = 40;

  // TODO: may need to tune this and make sure that this encoding not optimized away.
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
  parameter int OtpCmdWidth      = 2;
  parameter int OtpSizeWidth     = 2; // Allows to transfer up to 4 native OTP words at once.
  parameter int OtpErrWidth      = 4;
  parameter int OtpIfWidth       = 2**OtpSizeWidth*OtpWidth;
  // Number of Byte address bits to cut off in order to get the native OTP word address.
  parameter int OtpAddrShift     = OtpByteAddrWidth - OtpAddrWidth;

  typedef enum logic [OtpCmdWidth-1:0] {
    OtpRead  = 2'b00,
    OtpWrite = 2'b01,
    OtpInit  = 2'b11
  } prim_otp_cmd_e;

  typedef enum logic [OtpErrWidth-1:0] {
    NoErr            = 4'h0,
    OtpCmdInvErr     = 4'h1,
    OtpInitErr       = 4'h2,
    OtpReadCorrErr   = 4'h3,
    OtpReadUncorrErr = 4'h4,
    OtpReadErr       = 4'h5,
    OtpWriteBlankErr = 4'h6,
    OtpWriteErr      = 4'h7,
    CmdInvErr        = 4'h8,
    AccessErr        = 4'h9,
    ParityErr        = 4'hA,
    IntegErr         = 4'hB,
    CnstyErr         = 4'hC,
    FsmErr           = 4'hD,
    EscErr           = 4'hE
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

  ////////////////////////
  // Partition Metadata //
  ////////////////////////

  typedef enum logic {
    Unbuffered,
    Buffered
  } part_variant_e;

  typedef struct packed {
    part_variant_e variant;
    // Offset and size within the OTP array, in Bytes.
    logic [OtpByteAddrWidth-1:0] offset;
    logic [OtpByteAddrWidth-1:0] size;
    // Key index to use for scrambling.
    logic [ConstSelWidth-1:0] key_idx;
    // Attributes
    logic scrambled;  // Whether the partition is scrambled
    logic hw_digest;  // Whether the partition has a hardware digest
    logic write_lock; // Whether the partition is write lockable (via digest)
    logic read_lock;  // Whether the partition is read lockable (via digest)
  } part_info_t;

  // TODO: need to parse this somehow from an hjson
  localparam part_info_t PartInfo [NumPart] = '{
    // Variant    | offset | size | key_idx | scrambled | HW digest | write_lock | read_lock
    // CREATOR_SW_CFG
    '{Unbuffered,   11'h0,   768,      0,       1'b0,      1'b0,      1'b1,       1'b0},
    // OWNER_SW_CFG
    '{Unbuffered,   11'h300, 768,      0,       1'b0,      1'b0,      1'b1,       1'b0},
    // HW_CFG
    '{Buffered,     11'h600, 176,      0,       1'b0,      1'b1,      1'b1,       1'b0},
    // SECRET0
    '{Buffered,     11'h6B0, 40,       0,       1'b1,      1'b1,      1'b1,       1'b1},
    // SECRET1
    '{Buffered,     11'h6D8, 88,       1,       1'b1,      1'b1,      1'b1,       1'b1},
    // SECRET2
    '{Buffered,     11'h730, 120,      2,       1'b1,      1'b1,      1'b1,       1'b1},
    // LIFE_CYCLE
    '{Buffered,     11'h7A8, 88,       0,       1'b0,      1'b0,      1'b0,       1'b0}
  };

  parameter int CreatorSwCfgIdx = 0;
  parameter int OwnerSwCfgIdx   = 1;
  parameter int HwCfgIdx        = 2;
  parameter int Secret0Idx      = 3;
  parameter int Secret1Idx      = 4;
  parameter int Secret2Idx      = 5;
  parameter int LifeCycleIdx    = 6;
  // These are not "real partitions", but in terms of implementation it is convenient to
  // add these at the end of certain arrays.
  parameter int DaiIdx = 7;
  parameter int LciIdx = 8;

  parameter int NumUnbuffered = 2;
  parameter int NumHwCfgBits = PartInfo[HwCfgIdx].size*8;

  ////////////////////////
  // Typedefs for CSRNG //
  ////////////////////////

  typedef struct packed {
    logic        en;
    logic [31:0] data;
  } otp_entropy_t;

  ///////////////////////////////
  // Typedefs for LC Interface //
  ///////////////////////////////

  parameter logic [127:0] LcTokenWidth = 128;

  // TODO: update this encoding and move to lc_ctrl_pkg
  typedef enum logic [15:0] {
    Blk = 16'h0000,
    Set = 16'hF5FA
  } lc_value_e;

  // TODO: move to lc_ctrl_pkg
  typedef enum lc_value_e [11:0] {
    LcStRaw           = {12{Blk}},
    LcStTestUnlocked0 = {Blk, Blk, Blk, Blk, Blk, Blk, Blk, Blk, Blk, Blk, Blk, Set},
    LcStTestLocked0   = {Blk, Blk, Blk, Blk, Blk, Blk, Blk, Blk, Blk, Blk, Set, Set},
    LcStTestUnlocked1 = {Blk, Blk, Blk, Blk, Blk, Blk, Blk, Blk, Blk, Set, Set, Set},
    LcStTestLocked1   = {Blk, Blk, Blk, Blk, Blk, Blk, Blk, Blk, Set, Set, Set, Set},
    LcStTestUnlocked2 = {Blk, Blk, Blk, Blk, Blk, Blk, Blk, Set, Set, Set, Set, Set},
    LcStTestLocked2   = {Blk, Blk, Blk, Blk, Blk, Blk, Set, Set, Set, Set, Set, Set},
    LcStTestUnlocked3 = {Blk, Blk, Blk, Blk, Blk, Set, Set, Set, Set, Set, Set, Set},
    LcStDev           = {Blk, Blk, Blk, Blk, Set, Set, Set, Set, Set, Set, Set, Set},
    LcStProd          = {Blk, Blk, Blk, Set, Blk, Set, Set, Set, Set, Set, Set, Set},
    LcStProdEnd       = {Blk, Blk, Set, Blk, Blk, Set, Set, Set, Set, Set, Set, Set},
    LcStRma           = {Set, Set, Blk, Set, Set, Set, Set, Set, Set, Set, Set, Set},
    LcStScrap         = {12{Set}}
  } lc_state_e;

  typedef struct packed {
    logic                    state_valid;
    logic                    test_token_valid;
    logic                    rma_token_valid;
    logic                    id_state_valid;
    lc_state_e               state;
    lc_value_e [31:0]        transition_count;
    logic [LcTokenWidth-1:0] test_unlock_token;
    logic [LcTokenWidth-1:0] test_exit_token;
    logic [LcTokenWidth-1:0] rma_token;
    lc_value_e               id_state;
  } otp_lc_data_t;  // broadcast

  typedef struct packed {
    // The LC controller signals the differential
    // with respect to the current state.
    logic         req;
    otp_lc_data_t diff;
  } lc_otp_program_req_t;

  typedef struct packed {
    logic  ack;
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
  parameter int SramKeyWidth  = 128;

  parameter int FlashKeySeedWidth = 256;
  parameter int SramKeySeedWidth  = 128;

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

  typedef struct packed {
    logic valid;
    logic [SramKeyWidth-1:0] addr_key;
    logic [SramKeyWidth-1:0] data_key;
  } sram_key_t;


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

endpackage : otp_ctrl_pkg


