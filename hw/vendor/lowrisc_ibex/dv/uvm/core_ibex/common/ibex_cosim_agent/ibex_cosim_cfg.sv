// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class core_ibex_cosim_cfg extends uvm_object;
  string     isa_string;
  bit [31:0] start_pc;
  bit [31:0] start_mtvec;
  bit        probe_imem_for_errs;
  string     log_file;

  `uvm_object_utils_begin(core_ibex_cosim_cfg)
    `uvm_field_string(isa_string, UVM_DEFAULT)
    `uvm_field_int(start_pc,    UVM_DEFAULT)
    `uvm_field_int(start_mtvec, UVM_DEFAULT)
    `uvm_field_int(probe_imem_for_errs, UVM_DEFAULT)
    `uvm_field_string(log_file, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new
endclass
