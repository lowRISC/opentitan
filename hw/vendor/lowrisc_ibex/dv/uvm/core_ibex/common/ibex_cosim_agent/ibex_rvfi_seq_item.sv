// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_rvfi_seq_item extends uvm_sequence_item;
  bit        trap;
  bit [31:0] pc;
  bit [4:0]  rd_addr;
  bit [31:0] rd_wdata;
  bit [63:0] order;
  bit [31:0] mip;
  bit        nmi;
  bit        nmi_int;
  bit        debug_req;
  bit        rf_wr_suppress;
  bit [63:0] mcycle;

  bit [31:0] mhpmcounters  [10];
  bit [31:0] mhpmcountersh [10];
  bit        ic_scr_key_valid;

  `uvm_object_utils_begin(ibex_rvfi_seq_item)
    `uvm_field_int (trap, UVM_DEFAULT)
    `uvm_field_int (pc, UVM_DEFAULT)
    `uvm_field_int (rd_addr, UVM_DEFAULT)
    `uvm_field_int (rd_wdata, UVM_DEFAULT)
    `uvm_field_int (order, UVM_DEFAULT)
    `uvm_field_int (mip, UVM_DEFAULT)
    `uvm_field_int (nmi, UVM_DEFAULT)
    `uvm_field_int (nmi_int, UVM_DEFAULT)
    `uvm_field_int (debug_req, UVM_DEFAULT)
    `uvm_field_int (rf_wr_suppress, UVM_DEFAULT)
    `uvm_field_int (mcycle, UVM_DEFAULT)
    `uvm_field_sarray_int (mhpmcounters, UVM_DEFAULT)
    `uvm_field_sarray_int (mhpmcountersh, UVM_DEFAULT)
    `uvm_field_int (ic_scr_key_valid, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass : ibex_rvfi_seq_item
