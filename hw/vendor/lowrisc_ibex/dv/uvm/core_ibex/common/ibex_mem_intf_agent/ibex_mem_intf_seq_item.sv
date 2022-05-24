// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//------------------------------------------------------------------------------
// CLASS: ibex_mem_intf_seq_item
//------------------------------------------------------------------------------

class ibex_mem_intf_seq_item extends uvm_sequence_item;

  rand bit [ADDR_WIDTH-1:0]     addr;
  rand rw_e                     read_write;
  rand bit [DATA_WIDTH-1:0]     data;
  rand bit [INTG_WIDTH-1:0]     intg;
  rand bit [DATA_WIDTH/8-1:0]   be;
  rand bit [3:0]                gnt_delay;
  rand bit [3:0]                req_delay;
  rand bit [5:0]                rvalid_delay;
  rand bit                      error;
       bit                      misaligned_first;
       bit                      misaligned_second;

  `uvm_object_utils_begin(ibex_mem_intf_seq_item)
    `uvm_field_int      (addr,              UVM_DEFAULT)
    `uvm_field_enum     (rw_e, read_write,  UVM_DEFAULT)
    `uvm_field_int      (be,                UVM_DEFAULT)
    `uvm_field_int      (data,             UVM_DEFAULT)
    `uvm_field_int      (intg,             UVM_DEFAULT)
    `uvm_field_int      (gnt_delay,         UVM_DEFAULT)
    `uvm_field_int      (rvalid_delay,      UVM_DEFAULT)
    `uvm_field_int      (error,             UVM_DEFAULT)
    `uvm_field_int      (misaligned_first,  UVM_DEFAULT)
    `uvm_field_int      (misaligned_second, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass : ibex_mem_intf_seq_item
