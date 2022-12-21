// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class core_ibex_env_cfg extends uvm_object;

  virtual clk_rst_if              ibex_clk_vif;
  virtual core_ibex_dut_probe_if  ibex_dut_vif;

  bit                           enable_mem_intg_err;
  bit                           enable_irq_single_seq;
  bit                           enable_irq_multiple_seq;
  bit                           enable_irq_nmi_seq;
  bit                           enable_nested_irq;
  bit                           enable_debug_seq;
  bit                           disable_fetch_enable_seq;
  bit                           disable_cosim;
  bit[31:0]                     max_interval;
  bit                           require_signature_addr;
  string                        signature_addr_str;
  bit[31:0]                     signature_addr;
  rand scrambling_key_agent_cfg scrambling_key_cfg;

  // Double-Fault detection in scoreboard
  bit                          enable_double_fault_detector = 1;
  int unsigned                 double_fault_threshold_consecutive = 100;
  int unsigned                 double_fault_threshold_total = 1000;
  // If '1', reaching either threshold fatally ends the test.
  // If '0', we end the test with a pass.
  bit                          is_double_fault_detected_fatal = 1;
  // If '1', reaching the timeout in seconds fatally ends the test.
  // If '0', we end the test with a pass.
  bit                          is_timeout_s_fatal = 1;

  `uvm_object_utils_begin(core_ibex_env_cfg)
    `uvm_field_int(enable_double_fault_detector, UVM_DEFAULT)
    `uvm_field_int(is_double_fault_detected_fatal, UVM_DEFAULT)
    `uvm_field_int(enable_mem_intg_err,   UVM_DEFAULT)
    `uvm_field_int(enable_irq_single_seq,   UVM_DEFAULT)
    `uvm_field_int(enable_irq_multiple_seq,   UVM_DEFAULT)
    `uvm_field_int(enable_irq_nmi_seq,   UVM_DEFAULT)
    `uvm_field_int(enable_nested_irq, UVM_DEFAULT)
    `uvm_field_int(enable_debug_seq, UVM_DEFAULT)
    `uvm_field_int(disable_fetch_enable_seq, UVM_DEFAULT)
    `uvm_field_int(disable_cosim, UVM_DEFAULT)
    `uvm_field_int(max_interval, UVM_DEFAULT)
    `uvm_field_int(require_signature_addr, UVM_DEFAULT)
    `uvm_field_int(signature_addr, UVM_DEFAULT)
    `uvm_field_object(scrambling_key_cfg, UVM_DEFAULT)
  `uvm_object_utils_end

  function new(string name = "");
    super.new(name);
    void'($value$plusargs("enable_double_fault_detector=%0d", enable_double_fault_detector));
    void'($value$plusargs("is_double_fault_detected_fatal=%0d", is_double_fault_detected_fatal));
    void'($value$plusargs("is_timeout_s_fatal=%0d", is_timeout_s_fatal));
    void'($value$plusargs("enable_mem_intg_err=%0d", enable_mem_intg_err));
    void'($value$plusargs("enable_irq_single_seq=%0d", enable_irq_single_seq));
    void'($value$plusargs("enable_irq_multiple_seq=%0d", enable_irq_multiple_seq));
    void'($value$plusargs("enable_irq_nmi_seq=%0d", enable_irq_nmi_seq));
    void'($value$plusargs("enable_nested_irq=%0d", enable_nested_irq));
    void'($value$plusargs("enable_debug_seq=%0d", enable_debug_seq));
    void'($value$plusargs("disable_fetch_enable_seq=%0d", disable_fetch_enable_seq));
    void'($value$plusargs("disable_cosim=%0d", disable_cosim));
    void'($value$plusargs("max_interval=%0d", max_interval));
    void'($value$plusargs("require_signature_addr=%0d", require_signature_addr));
    void'($value$plusargs("signature_addr=%s", signature_addr_str));
    signature_addr = signature_addr_str.atohex();
    scrambling_key_cfg = scrambling_key_agent_cfg::type_id::create("scrambling_key_cfg");
  endfunction

endclass
