// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Interface for the DUT's miscellaneous life cycle, RMA, key manager and power manager signals,
// which have no UVM agent attached.
//
// All inputs to the DUT are driven to known values from time zero, because the DUT asserts that
// all of its outputs are known (rram_ctrl.sv's ASSERT_KNOWN checks), which can only hold for
// known inputs.
interface rram_ctrl_misc_io_if(
  input logic clk,
  input logic rst_n
);
  // Packages defining the types of the DUT signals below
  import lc_ctrl_pkg::*;

  // Life cycle decoded enables.
  // The DUT synchronizes them into its own clock domain, so they can change at any time.
  lc_tx_t lc_creator_seed_sw_rw_en = On;
  lc_tx_t lc_owner_seed_sw_rw_en   = On;
  lc_tx_t lc_iso_part_sw_rd_en     = On;
  lc_tx_t lc_iso_part_sw_wr_en     = On;
  lc_tx_t lc_seed_hw_rd_en         = Off;
  lc_tx_t lc_escalate_en           = Off;
  lc_tx_t lc_nvm_debug_en          = Off;

  // RMA request from the life cycle controller.
  lc_tx_t           rma_req  = Off;
  lc_nvm_rma_seed_t rma_seed = LC_NVM_RMA_SEED_DEFAULT;
  lc_tx_t           rma_ack;

  // Seeds to the key manager.
  keymgr_dpe_pkg::keymgr_dpe_creator_seed_t keymgr_creator_seed;
  keymgr_dpe_pkg::keymgr_dpe_owner_seed_t   keymgr_owner_seed;

  // Power manager indication.
  pwrmgr_pkg::pwr_nvm_t pwrmgr;

  // Used to drive the RMA request and sample its acknowledgement without racing the DUT's own
  // posedge-triggered updates.
  clocking cb @(posedge clk);
    output rma_req, rma_seed;
    input  rma_ack;
  endclocking

  // Waits until the DUT reports that the RRAM is idle, sampled on clk.
  task automatic wait_nvm_idle();
    do @(posedge clk); while (pwrmgr.nvm_idle !== 1'b1);
  endtask

  // Waits until the DUT reports that the RRAM is busy, sampled on clk.
  task automatic wait_nvm_busy();
    do @(posedge clk); while (pwrmgr.nvm_idle !== 1'b0);
  endtask

endinterface : rram_ctrl_misc_io_if
