// Copyright lowRISC contributors (OpenTitan project).
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
  // $ ./util/design/gen-lfsr-seed.py --width 64 --seed 3296833456 --prefix ""
  parameter int LfsrWidth = 64;
  typedef logic [LfsrWidth-1:0] lfsr_seed_t;
  typedef logic [LfsrWidth-1:0][$clog2(LfsrWidth)-1:0] lfsr_perm_t;
  parameter lfsr_seed_t RndCnstLfsrSeedDefault = 64'hb496209a_10a81ea5;
  parameter lfsr_perm_t RndCnstLfsrPermDefault = {
    128'hf7963515_f8af8e60_fbfec4c0_f1edd9e2,
    256'h41e1c6d4_273d5046_2da7165d_1c1db882_693146c2_a33aa048_43762bed_0ecabea5
  };

  // The LFSR has an internal state width of 64 bits but we just use the lowest 32 bits of the
  // permuted state for initializing the RAM.
  parameter int LfsrOutWidth = 32;

  //////////////////////
  // Type definitions //
  //////////////////////

  typedef struct packed {
    logic                      valid;
    logic                      correctable;
    logic [top_pkg::TL_AW-1:0] address;
  } sram_error_t;

endpackage : sram_ctrl_pkg
