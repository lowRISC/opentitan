// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aon_timer_env_cfg extends cip_base_env_cfg #(.RAL_T(aon_timer_reg_block));

  virtual clk_rst_if        aon_clk_rst_vif;
  virtual pins_if #(1)      lc_escalate_en_vif;
  virtual pins_if #(2)      aon_intr_vif;
  virtual pins_if #(1)      sleep_vif;

  // ext component cfgs
  string  path_to_rtl = "tb.dut";

  `uvm_object_utils_begin(aon_timer_env_cfg)
  `uvm_object_utils_end

  extern function new (string name="");
  extern virtual function void initialize(bit [31:0] csr_base_addr = '1);
  // Set the 'has_prediction' field flag for all the intr_state fields so the comparison
  // on reads can be carried out in cip_base_scoreboard
  extern function void set_intr_state_has_prediction();

  // Convenience wrapper function to avoid calling explictly uvm_hdl_read multiple times
  // It takes a path relative to the RTL and appends the RTL instance to it
  extern function bit hdl_read_bit(string path);
  // Waits for AON signal to become 'value'
  extern task wait_for_aon_signal(string path, bit value);
  // Waits for the WE to rise and fall after a TL-UL write access
  // Does HDL reads to be in sync with when the values are visible in the RTL
  // It needs to be called the moment the TL-access occurs, otherwise the thread may hang if the WE
  // has risen and dropped again already
  extern task wait_for_we_pulse(input string path);

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
  // Allow mid-TL-US accesses
  can_reset_with_csr_accesses = 1;
endfunction : initialize

function bit aon_timer_env_cfg::hdl_read_bit(string path);
  bit   hdl_bit;
  if (! uvm_hdl_read({path_to_rtl,path}, hdl_bit))
    `uvm_error ($sformatf("%m"), $sformatf("HDL Read from %s failed", path))
  return hdl_bit;
endfunction

task aon_timer_env_cfg::wait_for_aon_signal(string path, bit value);
  bit actual_value;
  do begin
    actual_value = hdl_read_bit(path);
    if (actual_value !== value)
      aon_clk_rst_vif.wait_clks(1);
  end while (actual_value !== value);
endtask

task aon_timer_env_cfg::wait_for_we_pulse(input string path);
  wait_for_aon_signal(path, 1);
  wait_for_aon_signal(path, 0);
endtask

function void aon_timer_env_cfg::set_intr_state_has_prediction();
  foreach (ral_model_names[i]) begin
    dv_base_reg regs_q[$];
    ral_models[ral_model_names[i]].get_dv_base_regs(regs_q);
    foreach (regs_q[j]) begin
      if (!uvm_re_match("intr_state*", regs_q[j].get_name())) begin
        dv_base_reg_field fields_q[$];
        regs_q[j].get_dv_base_reg_fields(fields_q);
        foreach (fields_q[k])// Setting all fields to be compared in the base scoreboard
          fields_q[k].has_prediction = 1;
      end
    end
  end
endfunction
