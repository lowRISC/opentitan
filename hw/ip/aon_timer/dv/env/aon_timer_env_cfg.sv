// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aon_timer_env_cfg extends cip_base_env_cfg #(.RAL_T(aon_timer_reg_block));

  virtual clk_rst_if        aon_clk_rst_vif;
  virtual pins_if #(1)      lc_escalate_en_vif;
  virtual pins_if #(2)      aon_intr_vif;
  virtual pins_if #(1)      sleep_vif;

  // ext component cfgs

  `uvm_object_utils_begin(aon_timer_env_cfg)
  `uvm_object_utils_end

  extern function new (string name="");
  extern virtual function void initialize(bit [31:0] csr_base_addr = '1);
  extern function void set_intr_state_has_prediction();

endclass : aon_timer_env_cfg

function aon_timer_env_cfg::new (string name="");
  super.new(name);
endfunction : new

function void aon_timer_env_cfg::initialize(bit [31:0] csr_base_addr = '1);
  list_of_alerts = aon_timer_env_pkg::LIST_OF_ALERTS;
  super.initialize(csr_base_addr);

  m_tl_agent_cfg.max_outstanding_req = 1;

  // set num_interrupts & num_alerts
  num_interrupts = ral.intr_state.get_n_used_bits();
  set_intr_state_has_prediction();
endfunction : initialize

function void aon_timer_env_cfg::set_intr_state_has_prediction();
  dv_base_reg_field fields_q[$];
  dv_base_reg regs_q[$];
  string ral_name;
  foreach (ral_model_names[i]) begin
    ral_name = ral_model_names[i];
    ral_models[ral_name].get_dv_base_regs(regs_q);
    foreach (regs_q[j]) begin
      if (!uvm_re_match("intr_state*", regs_q[j].get_name())) begin
        regs_q[j].get_dv_base_reg_fields(fields_q);
         foreach (fields_q[k])// Setting all field to be compared in the base scoreboard
          fields_q[k].has_prediction = 1;
      end
    end
  end
endfunction
