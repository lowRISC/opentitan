// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_base_vseq extends cip_base_vseq #(
  .RAL_T              (pwm_reg_block),
  .CFG_T              (pwm_env_cfg),
  .COV_T              (pwm_env_cov),
  .VIRTUAL_SEQUENCER_T(pwm_virtual_sequencer)
);
  `uvm_object_utils(pwm_base_vseq)
  `uvm_object_new

  // random variables
  rand uint num_runs;

  // constraints
  constraint num_trans_c {
    num_trans inside {[cfg.seq_cfg.pwm_min_num_trans : cfg.seq_cfg.pwm_max_num_trans]};
  }
  constraint num_runs_c {
    num_runs inside {[cfg.seq_cfg.pwm_min_num_runs : cfg.seq_cfg.pwm_max_num_runs]};
  }

  virtual task pre_start();
    cfg.m_pwm_agent_cfg.en_monitor = cfg.en_scb;
    `uvm_info(`gfn, $sformatf("\n--> %s monitor and scoreboard", cfg.en_scb ? "enable" : "disable"),
              UVM_DEBUG)
    num_runs.rand_mode(0);
    // unset to disable intr test because pwm does not have intr pins
    do_clear_all_interrupts = 1'b0;
    super.pre_start();
  endtask : pre_start

  // setup basic pwm features
  virtual task pwm_init();
    // TODO
  endtask : pwm_init

  virtual task body();
    `uvm_info(`gfn, "\n--> start of sequence", UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("\n--> total required pulses %0d", num_trans), UVM_DEBUG)
    // TODO
  endtask : body

  // override apply_reset to handle core_reset domain
  virtual task apply_reset(string kind = "HARD");
    fork
      if (kind == "HARD" || kind == "TL_IF") begin
        super.apply_reset("HARD");
      end
      if (kind == "HARD" || kind == "CORE_IF") begin
        cfg.clk_rst_core_vif.apply_reset();
      end
    join
  endtask : apply_reset

  // phase alignment for resets signal of core and bus domain
  virtual task do_phase_align_reset(bit do_phase_align = 1'b0);
    if (do_phase_align) begin
      fork
        cfg.clk_rst_vif.wait_clks($urandom_range(5, 10));
        cfg.clk_rst_core_vif.wait_clks($urandom_range(5, 10));
      join
    end
  endtask : do_phase_align_reset

endclass : pwm_base_vseq
