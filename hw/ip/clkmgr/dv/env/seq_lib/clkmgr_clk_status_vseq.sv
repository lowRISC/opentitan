// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This tests the transitions of clk_status under various scenarios:
// - Transitions with ip_clk_en going active, assuming the usb clock is either active or inactive.
// - Transitions with ip_clk_en going inactive, and assumming any subset of the clocks
//   remain enabled (per controls in pwrmgr `control` CSR).
class clkmgr_clk_status_vseq extends clkmgr_base_vseq;
  `uvm_object_utils(clkmgr_clk_status_vseq)

  `uvm_object_new

  rand logic usb_clk_en_active;

  // If usb_clk_en_active is off we stop the incoming usb clock.
  task control_clocks();
    if (usb_clk_en_active) cfg.usb_clk_rst_vif.start_clk();
    else cfg.usb_clk_rst_vif.stop_clk();
  endtask

  function string create_failure_report();
    return $sformatf(
        "With ip_clk_en=%b, usb_clk_en_active=%b, clk_status is unexpectedly %b",
        ip_clk_en,
        usb_clk_en_active,
        cfg.clkmgr_vif.pwr_o.clk_status
    );
  endfunction

  task body();
    update_csrs_with_reset_values();
    for (int i = 0; i < num_trans; ++i) begin
      cfg.clk_rst_vif.wait_clks(4);
      `DV_CHECK_RANDOMIZE_FATAL(this)
      cfg.clkmgr_vif.init(.idle(idle), .ip_clk_en(ip_clk_en), .scanmode(scanmode));
      control_clocks();
      cfg.clk_rst_vif.wait_clks(10);
      // If some units were not idle, make them so.
      idle = '1;
      // Wait for idle to percolate.
      cfg.clk_rst_vif.wait_clks(10);
      `DV_CHECK_EQ(cfg.clkmgr_vif.pwr_o.clk_status, ip_clk_en, create_failure_report())
      // And set it back to a more common value for stress tests.
      ip_clk_en = 1'b1;
      usb_clk_en_active = 1'b1;
      cfg.clkmgr_vif.init(.idle(idle), .ip_clk_en(ip_clk_en), .scanmode(scanmode));
      control_clocks();
      cfg.clk_rst_vif.wait_clks(10);
    end
  endtask : body
endclass : clkmgr_clk_status_vseq
