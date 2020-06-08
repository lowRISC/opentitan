// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Utility macros

`ifndef PRIM_UTIL_SVH
`define PRIM_UTIL_SVH

/**
 * Math function: Number of bits needed to address |value| items.
 *
 *                  0        for value == 0
 * vbits =          1        for value == 1
 *         ceil(log2(value)) for value > 1
 *
 *
 * The primary use case for this function is the definition of registers/arrays
 * which are wide enough to contain |value| items.
 *
 * This function identical to $clog2() for all input values except the value 1;
 * it could be considered an "enhanced" $clog2() function.
 *
 *
 * Example 1:
 *   parameter Items = 1;
 *   localparam ItemsWidth = vbits(Items); // 1
 *   logic [ItemsWidth-1:0] item_register; // items_register is now [0:0]
 *
 * Example 2:
 *   parameter Items = 64;
 *   localparam ItemsWidth = vbits(Items); // 6
 *   logic [ItemsWidth-1:0] item_register; // items_register is now [5:0]
 *
 * Note: If you want to store the number "value" inside a register, you need
 * a register with size vbits(value + 1), since you also need to store
 * the number 0.
 *
 * Example 3:
 *   logic [vbits(64)-1:0]     store_64_logic_values; // width is [5:0]
 *   logic [vbits(64 + 1)-1:0] store_number_64;       // width is [6:0]
 */
function automatic integer vbits(integer value);
  return (value == 1) ? 1 : $clog2(value);
endfunction

`endif // PRIM_UTIL_SVH
