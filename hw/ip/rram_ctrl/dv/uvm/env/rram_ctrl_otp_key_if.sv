// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Interface to the DUT's otp_ctrl scrambling-key handshake, driven by
// rram_ctrl_otp_key_driver.sv (see rram_ctrl_env.sv).
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

  // otp_ctrl scrambling-key handshake is driven by rram_ctrl_otp_key_driver.
  otp_ctrl_pkg::nvm_otp_key_req_t otp_key_req;
  otp_ctrl_pkg::nvm_otp_key_rsp_t otp_key_rsp;

  // Backs rram_ctrl_otp_key_driver's assumption that the DUT never asserts both lines at once.
  `ASSERT(AddrDataReqMutex_A, !(otp_key_req.addr_req && otp_key_req.data_req), clk, !rst_n)

  // Used by rram_ctrl_otp_key_driver to sample req and drive rsp without racing the DUT's own
  // posedge-triggered updates.
  clocking host_cb @(posedge clk);
    input  req = otp_key_req;
    output rsp = otp_key_rsp;
  endclocking

endinterface : rram_ctrl_otp_key_if
