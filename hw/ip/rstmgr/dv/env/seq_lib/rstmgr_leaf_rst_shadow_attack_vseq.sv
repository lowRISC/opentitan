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
  endtask // body

  task leaf_rst_attack(string npath, string gpath);
      wait(cfg.rstmgr_vif.resets_o.rst_sys_aon_n == 2'h3);
      add_glitch(gpath);
      wait_and_check(npath);
      remove_glitch(gpath);

      cfg.clk_rst_vif.wait_clks(10);
      apply_reset();
  endtask // leaf_rst_attach


  function void add_glitch(string path);
    string epath = {path, ".rst_en_o"};
    string opath = {path, ".leaf_rst_o"};

    `DV_CHECK(uvm_hdl_force(epath, prim_mubi_pkg::MuBi4True))
    `DV_CHECK(uvm_hdl_force(opath, 0))
  endfunction

  task wait_and_check(string path);
    prim_mubi_pkg::mubi4_t rst_en;
    logic leaf_rst;
    string epath = {path, ".rst_en_o"};
    string opath = {path, ".leaf_rst_o"};

    cfg.clk_rst_vif.wait_clks(10);

    `DV_CHECK(uvm_hdl_read(epath, rst_en))
    `DV_CHECK(uvm_hdl_read(opath, leaf_rst))

    `DV_CHECK_EQ_FATAL(rst_en, prim_mubi_pkg::MuBi4False,
                       $sformatf("%s value mismatch",epath))
    `DV_CHECK_EQ_FATAL(leaf_rst, 1,
                       $sformatf("%s value mismatch",opath))
  endtask // wait_and_check

  function void remove_glitch(string path);
    string spath = {path, "_shadowed"};
    string epath = {spath, ".rst_en_o"};
    string opath = {spath, ".leaf_rst_o"};

    `DV_CHECK(uvm_hdl_release(epath))
    `DV_CHECK(uvm_hdl_release(opath))
  endfunction

  // clean up glitch will create reset consistency error
  // in shadow leaf reset module
  task post_start();
    expect_fatal_alerts = 1;
    super.post_start();
  endtask

endclass // rstmgr_leaf_rst_shadow_attack_vseq
