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

  bit obj_raised      = 1'b0;
  bit under_pre_abort = 1'b0;

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
        reset();
        cfg.reset_deasserted();
        `uvm_info(`gfn, "out of reset", UVM_HIGH)
      end
      else begin
        // wait for a change to rst_n
        @(cfg.clk_rst_vif.rst_n);
      end
    end
  endtask

  virtual function void reset(string kind = "HARD");
    // reset the ral model
    if (cfg.has_ral) ral.reset(kind);
  endfunction

  virtual function void pre_abort();
    super.pre_abort();
    // use under_pre_abort flag to prevent deadloop described below:
    // when fatal_err occurred, it will skip check_phase. We add the additional check_phase call
    // here to help debugging. But if inside the check_phase there are UVM_ERRORs, and the err cnt
    // is larger than max_err_cnt, then check_phase will call pre_abort again. This will end up
    // creating a deadloop.
    if (has_uvm_fatal_occurred() && !under_pre_abort) begin
      under_pre_abort = 1;
      check_phase(m_current_phase);
      under_pre_abort = 0;
    end
  endfunction : pre_abort

endclass

