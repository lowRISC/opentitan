// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A sequence item that represents a bit twiddle.
//
// The item will wait <delay> other reads before taking effect. When it does take effect, it toggles
// 1 or 2 bits in the read value. If <two_bits> is true, the bits at positions <bit_pos0> and
// <bit_pos1> will be toggled. Otherwise, just the bit at <bit_pos0> will be.
//
// <bit_pos0> and <bit_pos1> are interpreted modulo the interface width in the driver, so don't need
// constraining.

class ibex_icache_ecc_item extends uvm_sequence_item;

  rand bit          two_bits;
  rand int unsigned bit_pos0;
  rand int unsigned bit_pos1;
  rand int unsigned delay;

  `uvm_object_utils_begin(ibex_icache_ecc_item)
    `uvm_field_int (two_bits, UVM_DEFAULT)
    `uvm_field_int (bit_pos0, UVM_DEFAULT)
    `uvm_field_int (bit_pos1, UVM_DEFAULT)
    `uvm_field_int (delay,    UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new
endclass
