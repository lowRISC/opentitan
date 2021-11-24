// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aon_timer_base_vseq extends cip_base_vseq #(
    .RAL_T               (aon_timer_reg_block),
    .CFG_T               (aon_timer_env_cfg),
    .COV_T               (aon_timer_env_cov),
    .VIRTUAL_SEQUENCER_T (aon_timer_virtual_sequencer)
  );
  `uvm_object_utils(aon_timer_base_vseq)

  // various knobs to enable certain routines
  rand bit do_aon_timer_init;

  // If this is set, the AON clock starts first and then the fast clock starts sometime later. If
  // not, they start in parallel. Since the fast clock is *much* quicker, the practical result is
  // that it starts first.
  // TODO: Issue #6821: temp set to 1 to avoid assertion error.
  // rand bit reset_aon_first;
  bit reset_aon_first = 1;

  // Should the escalation signal be enabled at the start of time?
  rand bit initial_lc_escalate_en;

  // Is the chip in sleep at the start of time? In the real chip, the answer is (obviously) no, but
  // the design should work either way so we may as well test it.
  rand bit initial_sleep_mode;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_aon_timer_init) aon_timer_init();
  endtask

  virtual task dut_shutdown();
    // check for pending aon_timer operations and wait for them to complete
    // TODO
  endtask

  // setup basic aon_timer features
  virtual task aon_timer_init();
    `uvm_info(`gfn, "Initializating aon timer, nothing to do at the moment", UVM_MEDIUM)
  endtask

  virtual task apply_reset(string kind = "HARD");
    cfg.lc_escalate_en_vif.drive(initial_lc_escalate_en);
    cfg.sleep_vif.drive(initial_sleep_mode);

    // Bring up the clocks in either order. We can't just race them by running them in parallel,
    // because the AON clock is much slower so will always come up second.
    if (kind == "HARD" && reset_aon_first) begin
      cfg.aon_clk_rst_vif.apply_reset();
      super.apply_reset(kind);
    end else begin
      fork
        if (kind == "HARD") cfg.aon_clk_rst_vif.apply_reset();
        super.apply_reset(kind);
      join
    end
  endtask // apply_reset

  virtual task apply_resets_concurrently(int reset_duration_ps = 0);
    cfg.aon_clk_rst_vif.drive_rst_pin(0);
    super.apply_resets_concurrently(cfg.aon_clk_rst_vif.clk_period_ps);
    cfg.aon_clk_rst_vif.drive_rst_pin(1);
  endtask
endclass : aon_timer_base_vseq
