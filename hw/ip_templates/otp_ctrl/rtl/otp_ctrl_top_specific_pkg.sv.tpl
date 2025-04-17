// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

// This package contains top specific and implementation items.
//
// It imports otp_ctrl_reg_pkg, which is generated from the top specific hjson file.
// The items that are generic and used by top-independent IPs are placed in otp_ctrl_pkg.
package otp_ctrl_top_specific_pkg;

  import prim_util_pkg::vbits;
  import otp_ctrl_pkg::*;
  import otp_ctrl_reg_pkg::*;
  import otp_ctrl_macro_pkg::OtpWidth;
  import otp_ctrl_macro_pkg::OtpErrWidth;

  ////////////////////////
  // General Parameters //
  ////////////////////////

  // Width of entropy input
  parameter int EdnDataWidth = 64;

  parameter int NumPartWidth = vbits(NumPart);

  parameter int SwWindowAddrWidth = vbits(NumSwCfgWindowWords);

  // Background check timer LFSR width.
  parameter int LfsrWidth = 40;
  // The LFSR will be reseeded once LfsrUsageThreshold
  // values have been drawn from it.
  parameter int LfsrUsageThreshold = 16;

  // Redundantly encoded and complementary values are used to for signalling to the partition
  // controller FSMs and the DAI whether a partition is locked or not. Any other value than
  // "Mubi8Lo" is interpreted as "Locked" in those FSMs.
  typedef struct packed {
    prim_mubi_pkg::mubi8_t read_lock;
    prim_mubi_pkg::mubi8_t write_lock;
  } part_access_t;

  parameter int DaiCmdWidth = 3;
  typedef enum logic [DaiCmdWidth-1:0] {
    DaiRead   = 3'b001,
    DaiWrite  = 3'b010,
    DaiDigest = 3'b100
  } dai_cmd_e;

  // Typedef for extended OTP Error. This extends the OTP macro errors.
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

  ////////////////////////////////
  // Typedefs for Key Broadcast //
  ////////////////////////////////

  // Get maximum nonce width
% if enable_flash_key:
  localparam int NumNonceChunks =
    (OtbnNonceWidth > FlashKeyWidth) ?
    ((OtbnNonceWidth > SramNonceWidth) ? OtbnNonceSel : SramNonceSel) :
    ((FlashKeyWidth > SramNonceWidth)  ? FlashNonceSel  : SramNonceSel);
% else:
  localparam int NumNonceChunks =
    (OtbnNonceWidth > SramNonceWidth) ? OtbnNonceSel : SramNonceSel;
% endif

  ///////////////////////////////////////////
  // Defaults for random netlist constants //
  ///////////////////////////////////////////

  // These LFSR parameters have been generated with
  // $ util/design/gen-lfsr-seed.py --width 40 --seed 4247488366
  typedef logic [LfsrWidth-1:0]                        lfsr_seed_t;
  typedef logic [LfsrWidth-1:0][$clog2(LfsrWidth)-1:0] lfsr_perm_t;
  localparam lfsr_seed_t RndCnstLfsrSeedDefault = 40'h453d28ea98;
  localparam lfsr_perm_t RndCnstLfsrPermDefault =
      240'h4235171482c225f79289b32181a0163a760355d3447063d16661e44c12a5;

  typedef struct packed {
    sram_key_t   key;
    sram_nonce_t nonce;
  } scrmbl_key_init_t;
  localparam scrmbl_key_init_t RndCnstScrmblKeyInitDefault =
      256'hcebeb96ffe0eced795f8b2cfe23c1e519e4fa08047a6bcfb811b04f0a479006e;

endpackage : otp_ctrl_top_specific_pkg
