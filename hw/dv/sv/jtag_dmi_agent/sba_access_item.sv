// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sba_access_item extends uvm_sequence_item;
  // Request side signals.
  rand bus_op_e           bus_op;
  rand sba_access_size_e  size;
  rand logic [BUS_AW-1:0] addr;
  rand logic [BUS_DW-1:0] wdata;

  // Special stimulus configuration knobs.
  rand logic readonaddr;
  rand logic readondata;
  rand logic autoincrement;

  constraint read_on_addr_or_data_c {
    soft (readonaddr || readondata);
  }

  constraint no_autoincrement_c {
    soft autoincrement == 0;
  }

  // Response side signals.
  rand logic [BUS_DW-1:0] rdata;
  rand  sba_access_err_e  is_err;
  rand logic              is_busy_err;
  rand logic              timed_out;

  `uvm_object_utils_begin(sba_access_item)
    `uvm_field_enum(bus_op_e, bus_op,         UVM_DEFAULT)
    `uvm_field_enum(sba_access_size_e, size,  UVM_DEFAULT)
    `uvm_field_int (addr,                     UVM_DEFAULT)
    `uvm_field_int (wdata,                    UVM_DEFAULT)
    `uvm_field_int (readonaddr,               UVM_DEFAULT)
    `uvm_field_int (readondata,               UVM_DEFAULT)
    `uvm_field_int (autoincrement,            UVM_DEFAULT)
    `uvm_field_int (rdata,                    UVM_DEFAULT)
    `uvm_field_int (is_busy_err,              UVM_DEFAULT)
    `uvm_field_enum(sba_access_err_e, is_err, UVM_DEFAULT)
    `uvm_field_int (timed_out,                UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void disable_req_randomization();
    bus_op.rand_mode(0);
    addr.rand_mode(0);
    size.rand_mode(0);
    wdata.rand_mode(0);
    readonaddr.rand_mode(0);
    readondata.rand_mode(0);
    autoincrement.rand_mode(0);
  endfunction

  virtual function void disable_rsp_randomization();
    rdata.rand_mode(0);
    is_err.rand_mode(0);
    is_busy_err.rand_mode(0);
    timed_out.rand_mode(0);
  endfunction

endclass
