// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sba_access_item extends uvm_sequence_item;
  // Request side signals.
  rand bus_op_e           bus_op;
  rand sba_access_size_e  size;
  rand logic [BUS_AW-1:0] addr;
  rand logic [BUS_DW-1:0] wdata[$];

  // Special stimulus configuration knobs.
  rand logic readonaddr;
  rand logic readondata;

  // Have the design autoincrement the address.
  //
  // If set to 0, the autoincrement feature is disabled and a single access is made. If set to N (N
  // > 0), N + 1 accesses are made by the sba_access_utils_pkg::sba_acess() task. This is only used
  // during the generation of stimulus. It is not used by the sba_access_monitor.
  uint autoincrement;

  // Response side signals.
  logic [BUS_DW-1:0] rdata[$];
  sba_access_err_e   is_err;
  logic              is_busy_err;
  logic              timed_out;

  constraint wdata_size_c {
    wdata.size() == (autoincrement + 1);
  }

  `uvm_object_utils_begin(sba_access_item)
    `uvm_field_enum(bus_op_e, bus_op,         UVM_DEFAULT)
    `uvm_field_enum(sba_access_size_e, size,  UVM_DEFAULT)
    `uvm_field_int (addr,                     UVM_DEFAULT)
    `uvm_field_queue_int(wdata,               UVM_DEFAULT)
    `uvm_field_int (readonaddr,               UVM_DEFAULT)
    `uvm_field_int (readondata,               UVM_DEFAULT)
    `uvm_field_int (autoincrement,            UVM_DEFAULT)
    `uvm_field_queue_int(rdata,               UVM_DEFAULT)
    `uvm_field_int (is_busy_err,              UVM_DEFAULT)
    `uvm_field_enum(sba_access_err_e, is_err, UVM_DEFAULT)
    `uvm_field_int (timed_out,                UVM_DEFAULT)
  `uvm_object_utils_end

  function new (string name = "");
    super.new(name);
    is_err = SbaErrNone;
    is_busy_err = 0;
    timed_out = 0;
  endfunction : new

endclass
