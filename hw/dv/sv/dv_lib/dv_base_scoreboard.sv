// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`uvm_analysis_imp_decl(_scb_reset)

class dv_base_scoreboard #(type RAL_T = dv_base_reg_block,
                           type CFG_T = dv_base_env_cfg,
                           type COV_T = dv_base_env_cov) extends uvm_component;
  `uvm_component_param_utils(dv_base_scoreboard #(RAL_T, CFG_T, COV_T))

  CFG_T    cfg;
  RAL_T    ral;
  COV_T    cov;

  bit obj_raised      = 1'b0;
  bit under_pre_abort = 1'b0;

  uvm_analysis_imp_scb_reset #(reset_state_e, dv_base_scoreboard#(RAL_T,CFG_T, COV_T)) reset_st_imp;

  function new (string name="", uvm_component parent=null);
    super.new(name, parent);
    reset_st_imp = new ("reset_st_imp", this);
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ral = cfg.ral;
  endfunction

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      sample_resets();
    join_none
  endtask

  virtual function void write_scb_reset(reset_state_e reset_st);
    if (reset_st == ResetAsserted) begin
      reset();
    end
  endfunction : write_scb_reset

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
