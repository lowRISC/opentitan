// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package sram_ctrl_pkg;

  ////////////////
  // Parameters //
  ////////////////

  // The width of this RAM is currently restricted to 32.
  parameter int Width = 32;
  // This is later on pruned to the correct width at the SRAM wrapper interface.
  parameter int AddrWidth = 32;
  parameter int RandInitSeed = 32;
  parameter int NonceWidth = 64;
  typedef logic [RandInitSeed-1:0][$clog2(RandInitSeed)-1:0] lfsr_perm_t;

  /////////////
  // RndCnst //
  /////////////

  parameter otp_ctrl_pkg::sram_key_t RndCnstSramKeyDefault =
      128'hbecda03b34bc0418a30a33861a610f71;
  parameter otp_ctrl_pkg::sram_nonce_t RndCnstSramNonceDefault =
      128'h22f296f8f95efb84a75cd435a5541e9f;
  parameter lfsr_perm_t RndCnstSramLfsrPermDefault =
      160'h8c24f71703eda8a2378916b6bf80c76651ebcea1;

  /////////////////////
  // Interface Types //
  /////////////////////

  typedef struct packed {
    // TL-UL transactions to the SRAM will not be granted if valid = 0.
    logic                                    valid;
    logic [otp_ctrl_pkg::SramKeyWidth-1:0]   key;
    logic [NonceWidth-1:0]                   nonce;
  } sram_scr_req_t;

  typedef struct packed {
    logic                                    req;
    logic [RandInitSeed-1:0]                 seed;
  } sram_scr_init_req_t;

  typedef struct packed {
    logic [1:0]           rerror; // Bit1: Uncorrectable, Bit0: Correctable
    logic [AddrWidth-1:0] raddr;  // Read address for error reporting.
  } sram_scr_rsp_t;

  typedef struct packed {
    logic                  ack;
  } sram_scr_init_rsp_t;

endpackage : sram_ctrl_pkg
