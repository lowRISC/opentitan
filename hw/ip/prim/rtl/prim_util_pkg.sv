// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


/**
 * Utility functions
 */
package prim_util_pkg;
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

  /**
   * Computes the ceiling division of two integer values.
   *
   * This function performs integer division and rounds the result up to the nearest integer.
   * It effectively computes the smallest integer greater than or equal to dividend / divisor.
   *
   * @param dividend The integer dividend.
   * @param divisor The integer divisor.
   * @return The ceiling division result (dividend / divisor, rounded up).
   *
   * Example:
   * ceil_div(10, 3) returns 4
   * ceil_div(12, 4) returns 3
   * ceil_div(15, 6) returns 3
   */
  function automatic integer ceil_div(input integer dividend, input integer divisor);
    ceil_div = ((dividend % divisor) != 0) ? (dividend / divisor) + 1 : (dividend / divisor);
  endfunction

  // The lack of parametrized function arguments in SystemVerilog means that a maximum width of the
  // `countones` input has to be fixed.
  parameter int MaxCountOnesWidth = 1024;
  parameter int MaxCountOnesBits  = $clog2(MaxCountOnesWidth+1);

  /**
   * Count the number of set bits in a word.
   *
   * Effectively implements `$countones` which is not supported by all tools.
   *
   * @param word The input whose set bits are being counted
   * @return The number of set bits in `word`.
   */
  function automatic logic [MaxCountOnesBits-1:0] count_ones(
      input logic [MaxCountOnesWidth-1:0] word);
    logic [MaxCountOnesBits-1:0] count = '0;
    for (int i = 0; i < MaxCountOnesWidth; i++) begin
      count = count + MaxCountOnesBits'(word[i]);
    end
    return count;
  endfunction

`ifdef INC_ASSERT
  // Package-scoped variable to detect the end of simulation.
  //
  // Used only in DV simulations. The bit will be used by assertions in RTL to perform end-of-test
  // cleanup. It is set to 1 in `dv_test_status_pkg::dv_test_status()`, which is invoked right
  // before the simulation is terminated, to signal the status of the test.
  bit end_of_simulation;
`endif

endpackage
