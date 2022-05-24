// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_ifetch_pmp_seq_item extends uvm_sequence_item;
  bit [31:0] fetch_addr;
  bit        fetch_pmp_err;

  `uvm_object_utils_begin(ibex_ifetch_pmp_seq_item)
    `uvm_field_int (fetch_addr, UVM_DEFAULT)
    `uvm_field_int (fetch_pmp_err, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new
endclass : ibex_ifetch_pmp_seq_item
