// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sysrst_ctrl_base_vseq extends cip_base_vseq #(
    .RAL_T               (sysrst_ctrl_reg_block),
    .CFG_T               (sysrst_ctrl_env_cfg),
    .COV_T               (sysrst_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T (sysrst_ctrl_virtual_sequencer)
  );

  sysrst_ctrl_in_out_passthrough_seq m_sysrst_ctrl_in_out_passthrough_seq;
  
  `uvm_object_utils(sysrst_ctrl_base_vseq)

  // various knobs to enable certain routines
  bit do_sysrst_ctrl_init = 1'b1;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_sysrst_ctrl_init) sysrst_ctrl_init();
    add_delay_after_reset_before_csrs_access();
  endtask

  virtual task add_delay_after_reset_before_csrs_access();
    cfg.clk_rst_vif.wait_clks(2);
  endtask

  virtual task read_and_check_all_csrs_after_reset();
    add_delay_after_reset_before_csrs_access();
    super.read_and_check_all_csrs_after_reset();
  endtask

  virtual task dut_shutdown();
    // check for pending sysrst_ctrl operations and wait for them to complete
    // TODO
  endtask

  // setup basic sysrst_ctrl features
  virtual task sysrst_ctrl_init();
    `uvm_info(`gfn, "Setting up sysrst_ctrl", UVM_NONE)
  endtask

  virtual task apply_reset(string kind = "HARD");
    if (kind == "HARD") begin
      cfg.clk_aon_rst_vif.apply_reset();
    end
    super.apply_reset(kind);
  endtask  // apply_reset

  virtual task apply_resets_concurrently(int reset_duration_ps = 0);
    cfg.clk_aon_rst_vif.drive_rst_pin(0);
    super.apply_resets_concurrently(cfg.clk_aon_rst_vif.clk_period_ps);
    cfg.clk_aon_rst_vif.drive_rst_pin(1);
  endtask


endclass : sysrst_ctrl_base_vseq
