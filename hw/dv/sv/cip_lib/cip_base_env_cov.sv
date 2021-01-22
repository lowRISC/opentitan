// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// put these covergoups outside the class in order to create them anywhere after get cfg object
// if more than one interrupt/alert registers, these can be reused
// in extended cov class, better to have the covergroup inside the class and create in new function
covergroup intr_cg (uint num_interrupts) with function sample(uint intr,
                                                              bit intr_en,
                                                              bit intr_state);
  cp_intr: coverpoint intr {
    bins all_values[] = {[0:num_interrupts-1]};
  }
  cp_intr_en: coverpoint intr_en;
  cp_intr_state: coverpoint intr_state;
  cross cp_intr, cp_intr_en, cp_intr_state;
endgroup

covergroup intr_test_cg (uint num_interrupts) with function sample(uint intr,
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
    illegal_bins test_1_state_0 = binsof(cp_intr_test) intersect {1} &&
                                  binsof(cp_intr_state) intersect {0};
  }
endgroup

covergroup intr_pins_cg (uint num_interrupts) with function sample(uint intr_pin,
                                                                   bit  intr_pin_value);
  cp_intr_pin: coverpoint intr_pin {
    bins all_pins[] = {[0:num_interrupts-1]};
  }
  cp_intr_pin_value: coverpoint intr_pin_value {
    bins values[] = {0, 1};
    bins transitions[] = (0 => 1), (1 => 0);
  }
  cp_intr_pins_all_values: cross cp_intr_pin, cp_intr_pin_value;
endgroup

class cip_base_env_cov #(type CFG_T = cip_base_env_cfg) extends dv_base_env_cov #(CFG_T);
  `uvm_component_param_utils(cip_base_env_cov #(CFG_T))

  intr_cg        intr_cg;
  intr_test_cg   intr_test_cg;
  intr_pins_cg   intr_pins_cg;
  // Coverage for sticky interrupt functionality described in CIP specification
  // As some interrupts are non-sticky, this covergroup should be populated on "as and when needed"
  // basis in extended <ip>_env_cov class for interrupt types that are sticky
  bit_toggle_cg_wrap sticky_intr_cov[string];

  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (cfg.num_interrupts != 0) begin
      intr_cg      = new(cfg.num_interrupts);
      intr_test_cg = new(cfg.num_interrupts);
      intr_pins_cg = new(cfg.num_interrupts);
    end
  endfunction

endclass
