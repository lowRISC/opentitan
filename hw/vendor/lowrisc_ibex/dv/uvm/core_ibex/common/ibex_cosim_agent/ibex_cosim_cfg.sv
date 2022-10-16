// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class core_ibex_cosim_cfg extends uvm_object;
  string     isa_string;
  bit [31:0] start_pc;
  bit [31:0] start_mtvec;
  bit        probe_imem_for_errs;
  string     log_file;
  bit [31:0] pmp_num_regions;
  bit [31:0] pmp_granularity;
  bit [31:0] mhpm_counter_num;
  bit        relax_cosim_check;
  bit        secure_ibex;
  bit        icache;

  `uvm_object_utils_begin(core_ibex_cosim_cfg)
    `uvm_field_string(isa_string, UVM_DEFAULT)
    `uvm_field_int(start_pc,    UVM_DEFAULT)
    `uvm_field_int(start_mtvec, UVM_DEFAULT)
    `uvm_field_int(probe_imem_for_errs, UVM_DEFAULT)
    `uvm_field_string(log_file, UVM_DEFAULT)
    `uvm_field_int(pmp_num_regions, UVM_DEFAULT)
    `uvm_field_int(pmp_granularity, UVM_DEFAULT)
    `uvm_field_int(mhpm_counter_num, UVM_DEFAULT)
    `uvm_field_int(secure_ibex, UVM_DEFAULT)
    `uvm_field_int(icache, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new
endclass
