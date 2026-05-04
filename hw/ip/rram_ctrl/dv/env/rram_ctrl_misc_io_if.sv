// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Interface to handle signal level code for the miscellaneous signals without an attached
// UVM agent
interface rram_ctrl_misc_io_if(
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

  // Imports from packages
  import lc_ctrl_pkg::*;
  import rram_ctrl_pkg::*;
  import otp_ctrl_pkg::*;
  import otp_ctrl_macro_pkg::*;
  import ast_pkg::*;

  // Variables corresponding to some of the DUT signals
  lc_tx_t  lc_creator_seed_sw_rw_en = lc_ctrl_pkg::On;
  lc_tx_t  lc_owner_seed_sw_rw_en   = lc_ctrl_pkg::On;
  lc_tx_t  lc_seed_hw_rd_en         = lc_ctrl_pkg::Off;

  lc_tx_t  lc_iso_part_sw_rd_en = lc_ctrl_pkg::On;
  lc_tx_t  lc_iso_part_sw_wr_en = lc_ctrl_pkg::On;

  lc_tx_t  lc_nvm_debug_en = lc_ctrl_pkg::Off;
  lc_tx_t  lc_escalate_en  = lc_ctrl_pkg::Off;

  keymgr_rram_t keymgr;

  pwrmgr_pkg::pwr_nvm_t pwr_nvm;

  lc_tx_t           rma_req;
  lc_nvm_rma_seed_t rma_seed;
  lc_tx_t           rma_ack;

  otp_ctrl_pkg::nvm_otp_key_req_t otp_key_req;
  otp_ctrl_pkg::nvm_otp_key_rsp_t otp_key_rsp;

  otp_ctrl_macro_pkg::otp_ctrl_macro_req_t otp_macro_req;
  otp_ctrl_macro_pkg::otp_ctrl_macro_rsp_t otp_macro_rsp;

  clocking cb @(posedge clk);
    default input #1step output #2;
    output    rma_req, rma_seed;
    input     rma_ack;
  endclocking

endinterface : rram_ctrl_misc_io_if
