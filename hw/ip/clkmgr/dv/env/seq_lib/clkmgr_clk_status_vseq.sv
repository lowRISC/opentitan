// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This tests the transitions of clk_status under various scenarios:
// - Transitions with ip_clk_en going active, assuming the usb clock is either active or inactive.
// - Transitions with ip_clk_en going inactive, and assumming any subset of the clocks
//   remain enabled (per controls in pwrmgr `control` CSR).
//
// The checks are done via SVA in clkmgr_pwrmgr_sva_if.
class clkmgr_clk_status_vseq extends clkmgr_base_vseq;
  `uvm_object_utils(clkmgr_clk_status_vseq)

  `uvm_object_new

  // And disable scanmode since it is not interesting.
  constraint scanmode_off_c {sel_scanmode == LcTxTSelOff;}

  task body();
    update_csrs_with_reset_values();
    for (int i = 0; i < num_trans; ++i) begin
      cfg.clk_rst_vif.wait_clks(4);
      `DV_CHECK_RANDOMIZE_FATAL(this)
      cfg.clkmgr_vif.init(.idle(idle), .scanmode(scanmode));
      control_ip_clocks();

      // If some units were not idle, make them so.
      idle = '1;
      // Wait for idle to percolate.
      cfg.clk_rst_vif.wait_clks(10);
    end
    // And set it back to more common values for stress tests.
    initialize_on_start();
  endtask : body
endclass : clkmgr_clk_status_vseq
