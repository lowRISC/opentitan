// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An item that represents a memory request from the icache and a possible update to the backing
// memory.

class ibex_icache_mem_req_item extends uvm_sequence_item;

  logic [31:0]      address;

  `uvm_object_utils_begin(ibex_icache_mem_req_item)
    `uvm_field_int (address,  UVM_DEFAULT | UVM_HEX)
  `uvm_object_utils_end

  `uvm_object_new
endclass
