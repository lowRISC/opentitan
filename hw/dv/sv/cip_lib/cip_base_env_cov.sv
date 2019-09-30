// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// put these covergoups outside the class in order to create them anywhere after get cfg object
// if more than one interrupt/alert registers, these can be reused
// in extended cov class, better to have the covergroup inside the class and create in new function
covergroup intr_covergroup (uint num_interrupts) with function sample(uint intr,
                                                                      bit intr_en,
                                                                      bit intr_state);
  cp_intr: coverpoint intr {
    bins all_values[] = {[0:num_interrupts-1]};
  }
  cp_intr_en: coverpoint intr_en;
  cp_intr_state: coverpoint intr_state;
  cross cp_intr, cp_intr_en, cp_intr_state;
endgroup

covergroup intr_test_covergroup (uint num_interrupts) with function sample(uint intr,
                                                                           bit intr_test,
                                                                           bit intr_en,
                                                                           bit intr_state);
  cp_intr: coverpoint intr {
    bins all_values[] = {[0:num_interrupts-1]};
  }
  cp_intr_test: coverpoint intr_test;
  cp_intr_en: coverpoint intr_en;
  cp_intr_state: coverpoint intr_state;
  cross cp_intr, cp_intr_test, cp_intr_en, cp_intr_state {
    illegal_bins test_0_state_1 = binsof(cp_intr_test) intersect {0} &&
                                  binsof(cp_intr_state) intersect {1};
  }
endgroup

covergroup alert_covergroup (uint num_alerts) with function sample(uint alert);
  cp_alert: coverpoint alert {
    bins all_values[] = {[0:num_alerts-1]};
  }
endgroup

class cip_base_env_cov #(type CFG_T = cip_base_env_cfg) extends dv_base_env_cov #(CFG_T);
  `uvm_component_param_utils(cip_base_env_cov #(CFG_T))

  intr_covergroup      intr_cg;
  intr_test_covergroup intr_test_cg;
  alert_covergroup     alert_cg;

  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (cfg.num_interrupts != 0) begin
      intr_cg       = new(cfg.num_interrupts);
      intr_test_cg  = new(cfg.num_interrupts);
    end
    if (cfg.num_alerts != 0) alert_cg = new(cfg.num_alerts);
  endfunction

endclass
