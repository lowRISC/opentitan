// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An item that represents a memory request from the icache and a possible update to the backing
// memory.
//
// When a request first comes in (via a posedge on the req line), it immediately generates a
// req_item with is_grant = 0. This is used by the sequence to tell the driver whether to generate a
// PMP error.
//
// Assuming that the request wasn't squashed by a PMP error, it will be granted on some later clock
// edge. At that point, another req_item is generated with is_grant = 1. This is added to a queue in
// the driver and will be serviced at some later point.

class ibex_icache_mem_req_item extends uvm_sequence_item;

  bit               is_grant;
  logic [31:0]      address;

  `uvm_object_utils_begin(ibex_icache_mem_req_item)
    `uvm_field_int (is_grant, UVM_DEFAULT)
    `uvm_field_int (address,  UVM_DEFAULT | UVM_HEX)
  `uvm_object_utils_end

  `uvm_object_new
endclass
