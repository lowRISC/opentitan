// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ibex_icache_core_bus_item extends uvm_sequence_item;

  // Type of bus transaction (branch, invalidate, fetch or busy)
  ibex_icache_core_bus_trans_type_e trans_type;

  // Address. For a branch transaction, this is the address of the destination. For a fetch
  // transaction, this is the address of the instruction fetched.
  logic [31:0]                      address;

  // 32 bits of data. Only has meaning for a fetch transaction, where it contains instruction data.
  logic [31:0]                      insn_data;

  // Error bits. Only have meaning for a fetch transaction
  logic                             err;
  logic                             err_plus2;

  // Cache configuration (is the cache enabled?). Only has meaning for an enable transaction.
  logic                             enable;

  // Busy bit. Only has meaning for a busy transaction, where it has the new value of the busy
  // signal.
  logic                             busy;

  `uvm_object_utils_begin(ibex_icache_core_bus_item)
    `uvm_field_enum(ibex_icache_core_bus_trans_type_e, trans_type, UVM_DEFAULT)
    `uvm_field_int(address,   UVM_DEFAULT | UVM_HEX)
    `uvm_field_int(insn_data, UVM_DEFAULT | UVM_HEX)
    `uvm_field_int(err,       UVM_DEFAULT)
    `uvm_field_int(err_plus2, UVM_DEFAULT)
    `uvm_field_int(enable,    UVM_DEFAULT)
    `uvm_field_int(busy,      UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

endclass
