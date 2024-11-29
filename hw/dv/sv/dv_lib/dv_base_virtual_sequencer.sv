// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Use this UVM macro as we may need to implement multiple uvm_analysis_imp, which means
// implemneting multiple write methods which is not possible with the same name.
`uvm_analysis_imp_decl(_vsqr_reset)

class dv_base_virtual_sequencer #(type CFG_T = dv_base_env_cfg,
                                  type COV_T = dv_base_env_cov) extends uvm_sequencer;
  `uvm_component_param_utils(dv_base_virtual_sequencer #(CFG_T, COV_T))

  CFG_T         cfg;
  COV_T         cov;

  uvm_analysis_imp_vsqr_reset #(
    reset_state_e, dv_base_virtual_sequencer#(CFG_T,COV_T)) reset_st_imp;

  function new (string name="", uvm_component parent=null);
    super.new(name, parent);
    reset_st_imp = new ("reset_st_imp", this);
  endfunction : new

  // This function will be executed each time the reset monitor will detect a reset activity. As
  // the monitor will broadcast this activity on a UVM TLM port uvm_analysis_port which is connected
  // to this component via a UVM analysis import.
  virtual function void write_vsqr_reset(reset_state_e reset_st);
    // TODO MVy: see if under_reset bit implementation is required or if fine to use the one from
    // cfg class.
  endfunction : write_vsqr_reset
endclass
