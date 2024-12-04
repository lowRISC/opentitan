// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package prim_xilinx_pkg;

  // Accommodates updatemem by breaking up flash info arrays into data and
  // metadata subarrays. The 76-bit width and 1 BRAM depth identifies these
  // memories in earlgrey, and we limit the subarray size to 64 bits, which is
  // the size of the data portion. The leftover 12 bits get placed into their
  // own memory with a unique hierarchical path. See prim_xilinx_ram_1p.sv to
  // see how this works.
  function automatic int get_ram_max_width(int width, int depth);
    if (width == 76 && depth < 4096) begin
      return 64;
    end
    return 0;
  endfunction

endpackage : prim_xilinx_pkg
