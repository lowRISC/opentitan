// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package sram_ctrl_pkg;

  ////////////////
  // Parameters //
  ////////////////

  // The width of this RAM is currently restricted to 39 (32bit data + 7bit integrity).
  parameter int DataWidth = 32 + tlul_pkg::DataIntgWidth;
  parameter int NonceWidth = 64;

  /////////////
  // RndCnst //
  /////////////

  parameter otp_ctrl_pkg::sram_key_t RndCnstSramKeyDefault =
      128'hbecda03b34bc0418a30a33861a610f71;
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramNonceDefault =
      128'h22f296f8f95efb84a75cd435a5541e9f;

  // These LFSR parameters have been generated with
  // $ ./util/design/gen-lfsr-seed.py --width 32 --seed 3296833456 --prefix ""
  parameter int LfsrWidth = 32;
  typedef logic [LfsrWidth-1:0] lfsr_seed_t;
  typedef logic [LfsrWidth-1:0][$clog2(LfsrWidth)-1:0] lfsr_perm_t;
  parameter lfsr_seed_t RndCnstLfsrSeedDefault = 32'h10a81ea5;
  parameter lfsr_perm_t RndCnstLfsrPermDefault = {
    160'h438131ae2cb71ffdd2e4c29a1f412231747cd7b2
  };


endpackage : sram_ctrl_pkg
