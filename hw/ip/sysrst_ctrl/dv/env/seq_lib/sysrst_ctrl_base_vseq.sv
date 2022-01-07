// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sysrst_ctrl_base_vseq extends cip_base_vseq #(
  .RAL_T              (sysrst_ctrl_reg_block),
  .CFG_T              (sysrst_ctrl_env_cfg),
  .COV_T              (sysrst_ctrl_env_cov),
  .VIRTUAL_SEQUENCER_T(sysrst_ctrl_virtual_sequencer)
);
  `uvm_object_utils(sysrst_ctrl_base_vseq)

  // various knobs to enable certain routines
  bit do_sysrst_ctrl_init = 1'b1;

  `uvm_object_new

  virtual task set_aon_clk_freq();
    cfg.clk_aon_rst_vif.set_freq_khz(200);
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    cfg.vif.reset_signals();
    super.dut_init();
    set_aon_clk_freq();
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
    // A place holder to add any basic feature or initialization in future
  endtask

  virtual task apply_reset(string kind = "HARD");
    if (kind == "HARD") begin
      fork
        super.apply_reset(kind);
        cfg.clk_aon_rst_vif.apply_reset(0,400,0,1);
      join
     // Ensure flash wp is in reset when opentitan is out of reset
     `DV_CHECK_EQ(cfg.vif.flash_wp_l, 0);
     // Ensure EC is in reset when OT is out of reset
     `DV_CHECK_EQ(cfg.vif.ec_rst_l_out, 0);
    end
  endtask  // apply_reset

  virtual task apply_resets_concurrently(int reset_duration_ps = 0);
    cfg.clk_aon_rst_vif.drive_rst_pin(0);
    super.apply_resets_concurrently(cfg.clk_aon_rst_vif.clk_period_ps);
    cfg.clk_aon_rst_vif.drive_rst_pin(1);
     `uvm_info(`gfn, "Driving from apply_resets_concurrently", UVM_NONE)
  endtask

endclass : sysrst_ctrl_base_vseq
