// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An item that represents a transaction seen on the interface.
//
// Since the interface is a bit weird here (bound in with forced data), we just report the address
// and data of each read transaction together with its XOR mask.

class ibex_icache_ecc_bus_item extends uvm_sequence_item;

  logic [31:0]  addr;
  logic [127:0] bad_bit_mask;
  logic [127:0] sram_rdata;

  `uvm_object_utils_begin(ibex_icache_ecc_bus_item)
    `uvm_field_int (bad_bit_mask, UVM_DEFAULT | UVM_HEX)
    `uvm_field_int (sram_rdata,   UVM_DEFAULT | UVM_HEX)
  `uvm_object_utils_end

  `uvm_object_new
endclass
