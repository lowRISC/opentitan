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

  parameter int RandInitSeed = 32;
  typedef logic [RandInitSeed-1:0][$clog2(RandInitSeed)-1:0] lfsr_perm_t;
  parameter lfsr_perm_t RndCnstSramLfsrPermDefault =
      160'h8c24f71703eda8a2378916b6bf80c76651ebcea1;

endpackage : sram_ctrl_pkg
