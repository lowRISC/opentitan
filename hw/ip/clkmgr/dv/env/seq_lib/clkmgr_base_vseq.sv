// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class clkmgr_base_vseq extends cip_base_vseq #(
    .RAL_T               (clkmgr_reg_block),
    .CFG_T               (clkmgr_env_cfg),
    .COV_T               (clkmgr_env_cov),
    .VIRTUAL_SEQUENCER_T (clkmgr_virtual_sequencer)
  );
  `uvm_object_utils(clkmgr_base_vseq)

  // various knobs to enable certain routines
  bit do_clkmgr_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_clkmgr_init) clkmgr_init();
  endtask

  virtual task dut_shutdown();
    // check for pending clkmgr operations and wait for them to complete
    // TODO
  endtask

  virtual task apply_reset(string reset_kind = "HARD");
    fork
      super.apply_reset(reset_kind);
      if (reset_kind == "HARD") fork
        cfg.main_clk_rst_vif.apply_reset();
        cfg.io_clk_rst_vif.apply_reset();
        cfg.usb_clk_rst_vif.apply_reset();
        cfg.aon_clk_rst_vif.apply_reset();
      join
    join
  endtask

  // setup basic clkmgr features
  virtual task clkmgr_init();
    // Initialize input clock frequencies.
    cfg.main_clk_rst_vif.set_freq_mhz(100);
    cfg.io_clk_rst_vif.set_freq_mhz(96);
    cfg.usb_clk_rst_vif.set_freq_mhz(48);
    cfg.aon_clk_rst_vif.set_freq_khz(200);
  endtask

endclass : clkmgr_base_vseq
