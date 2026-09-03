// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Interface to the DUT's otp_ctrl scrambling-key handshake, driven signal-level without
// an attached UVM agent
interface rram_ctrl_otp_key_if(
  input logic clk,
  input logic rst_n
);
  // Dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import rram_ctrl_env_pkg::*;
  import rram_ctrl_test_pkg::*;

  // Macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // Packages defining the types of the DUT signals below
  import otp_ctrl_pkg::*;

  // otp_ctrl scrambling-key handshake: otp_key_req <- DUT's otp_key_o, otp_key_rsp ->
  // DUT's otp_key_i. Modeled by otp_model() in rram_ctrl_base_vseq.sv.
  otp_ctrl_pkg::nvm_otp_key_req_t otp_key_req;
  otp_ctrl_pkg::nvm_otp_key_rsp_t otp_key_rsp;

endinterface : rram_ctrl_otp_key_if
