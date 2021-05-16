// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otbn_trace_item extends uvm_sequence_item;

  logic [31:0] insn_addr;

  `uvm_object_utils_begin(otbn_trace_item)
    `uvm_field_int  (insn_addr, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new
endclass
