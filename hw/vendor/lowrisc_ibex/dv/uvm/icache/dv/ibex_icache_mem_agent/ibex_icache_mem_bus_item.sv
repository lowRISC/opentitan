// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A transaction item that represents something happening on the memory bus. A 'request' is
// initiated by the cache and comes with an address. A 'response' comes from the memory system
// (including possibly the PMP checker). It comes with data and error flags.

class ibex_icache_mem_bus_item extends uvm_sequence_item;

  // What sort of transaction is this? (grant or response)
  bit          is_grant;

  // This holds the request address for a grant transaction and the returned rdata for a response
  // transaction.
  logic [31:0] data;

  // Response error flag (only valid for response transactions)
  logic        err;

  `uvm_object_utils_begin(ibex_icache_mem_bus_item)
    `uvm_field_int(is_grant, UVM_DEFAULT)
    `uvm_field_int(data,     UVM_DEFAULT | UVM_HEX)
    `uvm_field_int(err,      UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass
