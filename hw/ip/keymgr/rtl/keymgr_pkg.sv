// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// key manager package
//

package keymgr_pkg;

  parameter int KeyWidth = 256;
  parameter int OtbnKeyWidth = 384;
  parameter int KmacDataIfWidth = 64;  // KMAC interface data width
  parameter int SwBindingWidth = 32 * keymgr_reg_pkg::NumSwBindingReg;
  parameter int Shares = 2; // number of key shares

  typedef logic [KeyWidth-1:0] seed_t;

  // Default Lfsr configurations
  // These LFSR parameters have been generated with
  // $ util/design/gen-lfsr-seed.py --width 64 --seed 691876113 --prefix ""
  parameter int LfsrWidth = 64;
  typedef logic [LfsrWidth-1:0] lfsr_seed_t;
  typedef logic [LfsrWidth-1:0][$clog2(LfsrWidth)-1:0] lfsr_perm_t;
  parameter lfsr_seed_t RndCnstLfsrSeedDefault = 64'h22d326255bd24320;
  parameter lfsr_perm_t RndCnstLfsrPermDefault = {
    128'h16108c9f9008aa37e5118d1ec1df64a7,
    256'h24f3f1b73537f42d38383ee8f897286df81d49ab54b6bbbb666cbd1a16c41252
  };

  // Random permutation
  parameter int RandWidth = LfsrWidth / 2;
  typedef logic [RandWidth-1:0][$clog2(RandWidth)-1:0] rand_perm_t;
  parameter rand_perm_t RndCnstRandPermDefault = {
    160'h62089181d2a6be2ce145e2e27099ededbd7dceb0
  };

  // Key connection to various symmetric modules
  typedef struct packed {
    logic valid;
    logic [Shares-1:0][KeyWidth-1:0] key;
  } hw_key_req_t;

  // Key connection to otbn
  typedef struct packed {
    logic valid;
    logic [Shares-1:0][OtbnKeyWidth-1:0] key;
  } otbn_key_req_t;

  parameter hw_key_req_t HW_KEY_REQ_DEFAULT = '{
    valid: 1'b0,
    key: {Shares{KeyWidth'(32'hDEADBEEF)}}
  };

  parameter otbn_key_req_t OTBN_KEY_REQ_DEFAULT = '{
    valid: 1'b0,
    key: {Shares{OtbnKeyWidth'(32'hDEADBEEF)}}
  };

endpackage : keymgr_pkg
