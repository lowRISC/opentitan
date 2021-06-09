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
      sample_resets();
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
        csr_utils_pkg::clear_outstanding_access();
        `uvm_info(`gfn, "out of reset", UVM_HIGH)
      end
      else begin
        // wait for a change to rst_n
        @(cfg.clk_rst_vif.rst_n);
      end
    end
  endtask

  virtual task sample_resets();
    // Do nothing, actual coverage collection is under extended classes.
  endtask

  virtual function void reset(string kind = "HARD");
    // reset the ral model
    foreach (cfg.ral_models[i]) cfg.ral_models[i].reset(kind);
  endfunction

  virtual function void pre_abort();
    super.pre_abort();

    // In UVM, a fatal error normally aborts the test completely and skips the check phase. However,
    // it's sometimes helpful to run that phase on the scoreboard anyway (it might make it easier to
    // debug whatever went wrong), so we do that here.
    //
    // We only run the check phase if we were in the run phase: if something went wrong in the build
    // or connect phase, there's not much point in "checking the run" further. We also have to be
    // careful to avoid an infinite loop, so we set a flag to avoid doing this a second time if we
    // have errors in the check phase.
    if (has_uvm_fatal_occurred() &&
        !under_pre_abort &&
        m_current_phase.is(uvm_run_phase::get())) begin

      under_pre_abort = 1;
      check_phase(m_current_phase);
      under_pre_abort = 0;
    end
  endfunction : pre_abort

endclass

