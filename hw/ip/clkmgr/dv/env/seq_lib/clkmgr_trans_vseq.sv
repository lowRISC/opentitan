// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// trans test vseq
// This is a more randomized version of the corresponding test in the smoke sequence.
// FIXME Add randomized scanmode dut input.
class clkmgr_trans_vseq extends clkmgr_base_vseq;
  `uvm_object_utils(clkmgr_trans_vseq)

  `uvm_object_new

  rand bit [NUM_TRANS-1:0] initial_hints;

  // Starts with random units busy, set the hints at random. The idle units will be
  // disabled, but the others will remain enabled. Then all units are made idle.
  task body();
    trans_e trans;
    logic bit_value;
    logic [NUM_TRANS-1:0] value;

    cfg.clk_rst_vif.wait_clks(10);
    trans = trans.first;
    `uvm_info(`gfn, $sformatf("Updating hints to 0x%0x", initial_hints), UVM_MEDIUM)
    csr_wr(.ptr(ral.clk_hints), .value(initial_hints));
    update_hints(initial_hints);
    cfg.clkmgr_vif.wait_clks(5);
    csr_rd(.ptr(ral.clk_hints_status), .value(value));
    // We expect the status to be determined by hints and idle.
    `DV_CHECK_EQ(value, initial_hints | ~idle, "Busy units have status high")
    update_idle('1);
    cfg.clkmgr_vif.wait_clks(5);
    csr_rd(.ptr(ral.clk_hints_status), .value(value));
    `DV_CHECK_EQ(value, initial_hints, "All idle: units status matches hints")
    // Now enable them all.
    csr_wr(.ptr(ral.clk_hints), .value('1));
    update_hints('1);
    cfg.clkmgr_vif.wait_clks(5);
    csr_rd(.ptr(ral.clk_hints_status), .value(value));
    // We expect all units to be on.
    `DV_CHECK_EQ(value, '1, "All idle and all hints high: units status should be high")
  endtask : body

endclass : clkmgr_trans_vseq
