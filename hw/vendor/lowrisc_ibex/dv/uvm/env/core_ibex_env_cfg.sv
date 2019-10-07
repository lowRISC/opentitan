// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class core_ibex_env_cfg extends uvm_object;

  bit       enable_irq_seq;
  bit       enable_debug_stress_seq;
  bit       enable_debug_single_seq;
  bit[31:0] max_interval;
  bit       require_signature_addr;
  bit[31:0] signature_addr;

  `uvm_object_utils_begin(core_ibex_env_cfg)
    `uvm_field_int(enable_irq_seq,   UVM_DEFAULT)
    `uvm_field_int(enable_debug_single_seq, UVM_DEFAULT)
    `uvm_field_int(enable_debug_stress_seq, UVM_DEFAULT)
    `uvm_field_int(max_interval, UVM_DEFAULT)
    `uvm_field_int(require_signature_addr, UVM_DEFAULT)
    `uvm_field_int(signature_addr, UVM_DEFAULT)
  `uvm_object_utils_end

  function new(string name = "");
    super.new(name);
    void'($value$plusargs("enable_irq_seq=%0d", enable_irq_seq));
    void'($value$plusargs("enable_debug_stress_seq=%0d", enable_debug_stress_seq));
    void'($value$plusargs("enable_debug_single_seq=%0d", enable_debug_single_seq));
    void'($value$plusargs("max_interval=%0d", max_interval));
    void'($value$plusargs("require_signature_addr=%0d", require_signature_addr));
    void'($value$plusargs("signature_addr=%0h", signature_addr));
  endfunction

endclass
