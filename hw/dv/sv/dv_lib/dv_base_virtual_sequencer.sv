// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`uvm_analysis_imp_decl(_sqr_reset)

class dv_base_virtual_sequencer #(type CFG_T = dv_base_env_cfg,
                                  type COV_T = dv_base_env_cov) extends uvm_sequencer;
  `uvm_component_param_utils(dv_base_virtual_sequencer #(CFG_T, COV_T))

  CFG_T         cfg;
  COV_T         cov;

  uvm_analysis_imp_sqr_reset #(reset_state_e, dv_base_virtual_sequencer#(CFG_T,COV_T)) reset_st_imp;

  function new (string name="", uvm_component parent=null);
    super.new(name, parent);
    reset_st_imp = new ("reset_st_imp", this);
  endfunction : new

  virtual function void write_sqr_reset(reset_state_e reset_st);
    if (reset_st == ResetAsserted) begin
      cfg.reset_asserted();
    end else begin
      cfg.reset_deasserted();
      csr_utils_pkg::clear_outstanding_access();
    end
    `uvm_info(`gtn, $sformatf("Update reset state to %0s", reset_st.name()), UVM_DEBUG)
  endfunction : write_sqr_reset
endclass
