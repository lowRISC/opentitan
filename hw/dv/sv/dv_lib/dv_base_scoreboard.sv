// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dv_base_scoreboard #(type RAL_T = dv_base_reg_block,
                           type CFG_T = dv_base_env_cfg,
                           type COV_T = dv_base_env_cov) extends uvm_component;
  `uvm_component_param_utils(dv_base_scoreboard #(RAL_T, CFG_T, COV_T))

  CFG_T    cfg;
  RAL_T    ral;
  COV_T    cov;

  bit obj_raised = 1'b0;

  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ral = cfg.ral;
  endfunction

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      monitor_reset();
    join_none
  endtask

  virtual task monitor_reset();
    forever begin
      if (!cfg.clk_rst_vif.rst_n) begin
        `uvm_info(`gfn, "reset occurred", UVM_HIGH)
        cfg.reset_asserted();
        @(posedge cfg.clk_rst_vif.rst_n);
        cfg.reset_deasserted();
        reset();
        `uvm_info(`gfn, "out of reset", UVM_HIGH)
      end
      else begin
        // wait for a change to rst_n
        @(cfg.clk_rst_vif.rst_n);
      end
    end
  endtask

  // raise / drop objections based on certain events
  virtual function void process_objections(bit raise);
    if (raise && !obj_raised) begin
      `uvm_info(`gfn, "raising objection", UVM_HIGH)
      m_current_phase.raise_objection(this);
      obj_raised = 1'b1;
    end
    else if (!raise && obj_raised) begin
      `uvm_info(`gfn, "dropping objection", UVM_HIGH)
      m_current_phase.drop_objection(this);
      obj_raised = 1'b0;
    end
  endfunction

  virtual function void reset(string kind = "HARD");
    // reset the ral model
    if (cfg.has_ral) ral.reset(kind);
  endfunction

  virtual function void pre_abort();
    super.pre_abort();
    if (has_uvm_fatal_occurred()) check_phase(m_current_phase);
  endfunction : pre_abort

endclass

