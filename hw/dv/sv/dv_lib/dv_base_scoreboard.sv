// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Use this UVM macro as we may need to implement multiple uvm_analysis_imp, which means
// implemneting multiple write methods which is not possible with the same name.
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

  uvm_analysis_imp_scb_reset #(reset_state_e, dv_base_scoreboard#(RAL_T,CFG_T,COV_T)) reset_st_imp;

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

    // After each reset, the current transaction should be dropped and collect_trans should be
    // restarted once the reset is being deasserted.
    forever begin
      // This isolation fork is needed to ensure that "disable fork" call won't kill any other
      // processes at the same level from the base classes
      fork begin : isolation_fork
        fork
          begin : main_thread
            run_scoreboard();
            wait(0);  // Wait indefinitely to ensure the fork will end because of a reset detection
          end
          begin : reset_thread
            wait(cfg.under_reset);
            reset();  // This function is defined in most of the extended classes
          end
        join_any
        disable fork;   // Terminates all descendants and sub-descendants of isolation_fork
        wait(!cfg.under_reset);
      end join
    end
  endtask

  // This function will be executed each time the reset monitor will detect a reset activity. As
  // the monitor will broadcast this activity on a UVM TLM port uvm_analysis_port which is connected
  // to this component via a UVM analysis import.
  virtual function void write_scb_reset(reset_state_e reset_st);
    // Note: the under_reset signal from the dv_base_env_cfg class is managed from the SCB as this
    // component creation does not depend on any configuration knob and always exists.
    // TODO MVy: see if under_reset bit implementation is required or if fine to use the one from
    // cfg class.
    if (reset_st == ResetAsserted) begin
      cfg.reset_asserted();
      fork
        sample_resets();  // TODO MVy: see comment on function implementation below
      join_none
    end else begin
      cfg.reset_deasserted();
      csr_utils_pkg::clear_outstanding_access();
    end
    `uvm_info(`gtn, $sformatf("Update reset state to %0s", reset_st.name()), UVM_DEBUG)
  endfunction : write_scb_reset

  // TODO MVy: this can probably be removed from cip_base_scoreboard and the reset sampling can be
  // managed directly by the cip_base_env_cov as it extends from dv_base_env_cov which has now
  // access to the reset status directly if it implements write_cov_reset function
  virtual task sample_resets();
    // Do nothing, actual coverage collection is under extended classes.
  endtask

  virtual task run_scoreboard();
    // TODO MVy: Should be implemented by each extended scoreboards for their need instead of
    // directly calling the run_phase,. This will also allow them to drop their own reset monitoring
    // as already managed here.
  endtask : run_scoreboard

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
