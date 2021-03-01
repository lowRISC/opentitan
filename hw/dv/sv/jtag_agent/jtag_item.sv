// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class jtag_item extends uvm_sequence_item;

  // random variables
  rand uint ir_len;
  rand uint dr_len;

  rand logic [JTAG_IRW-1:0] ir;
  rand logic [JTAG_DRW-1:0] dr;
  rand logic [JTAG_DRW-1:0] dout;
  rand bit                  select_ir;

  constraint ir_len_c {
    ir_len <= JTAG_IRW;
  }

  constraint dr_len_c {
    dr_len <= JTAG_DRW;
  }

  `uvm_object_utils_begin(jtag_item)
    `uvm_field_int(ir_len, UVM_DEFAULT)
    `uvm_field_int(dr_len, UVM_DEFAULT)
    `uvm_field_int(ir,     UVM_DEFAULT)
    `uvm_field_int(dr,     UVM_DEFAULT)
    `uvm_field_int(dout,   UVM_DEFAULT)
    `uvm_field_int(select_ir,   UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass
