// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Description:
// Test assert glitch to shadow leaf reset module and
// check if nomal reset module got affected or vice versa
class rstmgr_leaf_rst_shadow_attack_vseq extends rstmgr_base_vseq;
  `uvm_object_utils(rstmgr_leaf_rst_shadow_attack_vseq)

  `uvm_object_new

  string leaf_path;

  task body();
    for (int i = 0; i < LIST_OF_SHADOW_LEAFS.size(); ++i) begin
      leaf_path = {"tb.dut.", LIST_OF_SHADOW_LEAFS[i]};
      `uvm_info(`gfn, $sformatf("Round %0d %s ", i, leaf_path), UVM_MEDIUM)

      leaf_rst_attack(leaf_path, {leaf_path, "_shadowed"});
      leaf_rst_attack({leaf_path, "_shadowed"}, leaf_path);
    end
  endtask : body

  task leaf_rst_attack(string npath, string gpath);
    // Wait for any bit in rst_sys_io_div4_n to become inactive.
    wait(|cfg.rstmgr_vif.resets_o.rst_sys_io_div4_n);
    // Disable cascading reset assertions, since forcing related signals causes failures.
    cfg.rstmgr_cascading_sva_vif.disable_sva = 1'b1;
    `uvm_info(`gfn, $sformatf("Starting leaf attack between %s and %s", npath, gpath), UVM_MEDIUM)
    cfg.scoreboard.set_exp_alert("fatal_cnsty_fault", 1, 20);
    add_glitch(gpath);
    wait_and_check(npath);
    remove_glitch(gpath);
    cfg.rstmgr_cascading_sva_vif.disable_sva = 1'b0;
    `uvm_info(`gfn, "Ending leaf attack", UVM_MEDIUM)

    cfg.clk_rst_vif.wait_clks(10);
    apply_reset();
  endtask : leaf_rst_attack


  function void add_glitch(string path);
    string epath = {path, ".rst_en_o"};
    string opath = {path, ".leaf_rst_o"};

    `DV_CHECK(uvm_hdl_force(epath, prim_mubi_pkg::MuBi4True), $sformatf(
              "Path %0s has problem", epath))
    `DV_CHECK(uvm_hdl_force(opath, 0), $sformatf("Path %0s has problem", opath))
  endfunction

  task wait_and_check(string path);
    prim_mubi_pkg::mubi4_t rst_en;
    logic leaf_rst;
    string epath = {path, ".rst_en_o"};
    string opath = {path, ".leaf_rst_o"};

    // Wait enough cycles to allow the uvm_hdl_force to take effect, since it is not instantaneous,
    // and for side-effects to propagate.
    cfg.io_div4_clk_rst_vif.wait_clks(10);

    `uvm_info(`gfn, $sformatf("Checking rst and en for %s", path), UVM_MEDIUM)
    `DV_CHECK(uvm_hdl_read(epath, rst_en), $sformatf("Path %0s has problem", epath))
    `DV_CHECK(uvm_hdl_read(opath, leaf_rst), $sformatf("Path %0s has problem", opath))

    `DV_CHECK_EQ(rst_en, prim_mubi_pkg::MuBi4False, $sformatf("%s value mismatch", epath))
    `DV_CHECK_EQ(leaf_rst, 1, $sformatf("%s value mismatch", opath))
  endtask : wait_and_check

  function void remove_glitch(string path);
    string epath = {path, ".rst_en_o"};
    string opath = {path, ".leaf_rst_o"};
    `DV_CHECK(uvm_hdl_release(epath), $sformatf("Path %0s has problem", epath))
    `DV_CHECK(uvm_hdl_release(opath), $sformatf("Path %0s has problem", opath))
  endfunction

  // clean up glitch will create reset consistency error
  // in shadow leaf reset module
  task post_start();
    expect_fatal_alerts = 1;
    super.post_start();
  endtask

endclass : rstmgr_leaf_rst_shadow_attack_vseq
