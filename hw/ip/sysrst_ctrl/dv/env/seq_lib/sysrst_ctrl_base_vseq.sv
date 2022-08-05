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
  rand bit en_intr;

  `uvm_object_new

  virtual task set_aon_clk_freq();
    cfg.clk_aon_rst_vif.set_freq_khz(200);
  endtask

  virtual task monitor_ec_rst_low(int exp_cycles);
    int act_cycles, wait_cycles;
    int aon_period_ns = cfg.clk_aon_rst_vif.clk_period_ps / 1000;
    // check ec_rst_l_out is low for exp_cycles. After exp_cycles+10, below will time out and fail.
    `DV_SPINWAIT(while(cfg.vif.ec_rst_l_out != 0) begin
                   cfg.clk_aon_rst_vif.wait_clks(1);
                   wait_cycles++;
                 end,"time out waiting for ec_rst == 0", aon_period_ns * 20)
    `DV_SPINWAIT(while (cfg.vif.ec_rst_l_out != 1) begin
                   cfg.clk_aon_rst_vif.wait_clks(1);
                   act_cycles++;
                 end,"time out waiting for ec_rst == 1",aon_period_ns * (exp_cycles + 3))
    `DV_CHECK(act_cycles inside {[exp_cycles - 3 : exp_cycles + 3]},
              $sformatf("act(%0d) vs exp(%0d) +/-3", act_cycles, exp_cycles))
  endtask

  virtual task driver_ec_rst_l_in(int cycles);
    cfg.vif.ec_rst_l_in = 0;
    // a few extra falling edges won't affect anything
    if ($urandom_range(0, 2)) begin
      cfg.clk_aon_rst_vif.wait_clks(1);
      cfg.vif.ec_rst_l_in = 1;
      cfg.clk_aon_rst_vif.wait_clks(1);
      cfg.vif.ec_rst_l_in = 0;
    end
    cfg.clk_aon_rst_vif.wait_clks(cycles);
    cfg.vif.ec_rst_l_in = 1;
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
    ral.intr_enable.event_detected.set(en_intr);
    csr_update(ral.intr_enable);
  endtask

  virtual task apply_reset(string kind = "HARD");
    if (kind == "HARD") begin
      fork
        super.apply_reset(kind);
        cfg.clk_aon_rst_vif.apply_reset(0,400,0,1);
      join
    end
  endtask  // apply_reset

  virtual task apply_resets_concurrently(int reset_duration_ps = 0);
    cfg.clk_aon_rst_vif.drive_rst_pin(0);
    super.apply_resets_concurrently(cfg.clk_aon_rst_vif.clk_period_ps);
    cfg.clk_aon_rst_vif.drive_rst_pin(1);
  endtask

endclass : sysrst_ctrl_base_vseq
