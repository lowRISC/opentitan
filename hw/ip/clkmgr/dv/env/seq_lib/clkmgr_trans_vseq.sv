// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// trans test vseq
// This is a more randomized version of the corresponding test in the smoke sequence.
// Starts with random units busy, set the hints at random. The idle units whose hint bit is off
// will be disabled, but the others will remain enabled. Then all units are made idle to check 
// that status matches hints. Prior to the next round this raises all hints to avoid units whose
// clock is off but are not idle.
class clkmgr_trans_vseq extends clkmgr_base_vseq;
  `uvm_object_utils(clkmgr_trans_vseq)

  `uvm_object_new

  rand bit [NUM_TRANS-1:0] initial_hints;

  task body();
    update_csrs_with_reset_values();
    for (int i = 0; i < num_trans; ++i) begin
      logic bit_value;
      logic [NUM_TRANS-1:0] value;

      `DV_CHECK_RANDOMIZE_FATAL(this)
      cfg.clkmgr_vif.init(.idle(idle), .ip_clk_en(ip_clk_en), .scanmode(scanmode));

      cfg.clk_rst_vif.wait_clks(10);
      `uvm_info(`gfn, $sformatf("Updating hints to 0x%0x", initial_hints), UVM_MEDIUM)
      csr_wr(.ptr(ral.clk_hints), .value(initial_hints));

      cfg.clk_rst_vif.wait_clks(5);
      // We expect the status to be determined by hints and idle.
      csr_rd(.ptr(ral.clk_hints_status), .value(value));
      `DV_CHECK_EQ(value, initial_hints | ~idle, "Busy units have status high")

      // Clearing idle should make hint_status match hints.
      cfg.clkmgr_vif.update_idle('1);
      cfg.clk_rst_vif.wait_clks(2);
      csr_rd(.ptr(ral.clk_hints_status), .value(value));
      `DV_CHECK_EQ(value, initial_hints, "All idle: units status matches hints")

      // Now set all hints, and the status should also be all ones.
      csr_wr(.ptr(ral.clk_hints), .value('1));
      cfg.clk_rst_vif.wait_clks(2);
      csr_rd(.ptr(ral.clk_hints_status), .value(value));
      // We expect all units to be on.
      `DV_CHECK_EQ(value, '1, "All idle and all hints high: units status should be high")
      csr_wr(.ptr(ral.clk_hints), .value(ral.clk_hints.get_reset()));
    end
  endtask : body

endclass : clkmgr_trans_vseq
