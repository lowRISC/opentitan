// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


/**
 * Utility functions
 */
package prim_util_pkg;
  /**
   * Math function: $clog2 as specified in Verilog-2005
   *
   * Do not use this function if $clog2() is available.
   *
   * clog2 =          0        for value == 0
   *         ceil(log2(value)) for value >= 1
   *
   * This implementation is a synthesizable variant of the $clog2 function as
   * specified in the Verilog-2005 standard (IEEE 1364-2005).
   *
   * To quote the standard:
   *   The system function $clog2 shall return the ceiling of the log
   *   base 2 of the argument (the log rounded up to an integer
   *   value). The argument can be an integer or an arbitrary sized
   *   vector value. The argument shall be treated as an unsigned
   *   value, and an argument value of 0 shall produce a result of 0.
   */
  function automatic integer _clog2(integer value);
    integer result;
    // Use an intermediate value to avoid assigning to an input port, which produces a warning in
    // Synopsys DC.
    integer v = value;
    v = v - 1;
    for (result = 0; v > 0; result++) begin
      v = v >> 1;
    end
    return result;
  endfunction


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
`ifdef XCELIUM
    // The use of system functions was not allowed here in Verilog-2001, but is
    // valid since (System)Verilog-2005, which is also when $clog2() first
    // appeared.
    // Xcelium < 19.10 does not yet support the use of $clog2() here, fall back
    // to an implementation without a system function. Remove this workaround
    // if we require a newer Xcelium version.
    // See #2579 and #2597.
    return (value == 1) ? 1 : _clog2(value);
`else
    return (value == 1) ? 1 : $clog2(value);
`endif
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
