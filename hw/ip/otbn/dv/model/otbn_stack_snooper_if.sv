// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Backdoor interface that can be bound into an OTBN stack and exports a function to peek at
// the stack contents.

`ifndef SYNTHESIS
interface otbn_stack_snooper_if #(
  parameter int StackWidth = 32,
  parameter int StackDepth = 4,
  localparam int StackDepthW = prim_util_pkg::vbits(StackDepth)
) (
  input logic [StackWidth-1:0] stack_storage [StackDepth],
  input logic [StackDepthW:0] stack_wr_ptr_q
);

  export "DPI-C" function otbn_stack_element_peek;

  function automatic int otbn_stack_element_peek(input int index, output bit [255:0] val);
    // Return 2 for issues indicating a broken usage of otbn_stack_element_peek
    // Function only works for stacks <= 256 bits wide
    if ((StackWidth > 256) || (index > StackDepth)) begin
      return 2;
    end

    // Return 1 where usage is correct but there's no more valid stack elements
    if (index >= stack_wr_ptr_q) begin
      return 1;
    end

    val = '0;
    val[StackWidth-1:0] = stack_storage[index];

    // Return 0 to indicate a valid stack element
    return 0;
  endfunction

endinterface
`endif // SYNTHESIS
