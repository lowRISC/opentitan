// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package prim_xilinx_pkg;

  // Returns the maximum width of an individual xpm memory. Note that this API
  // may evolve over time, but currently it uses the width and depth
  // parameters to identify memories that may need to be broken up into
  // separate groups. This can help work around updatemem's maximum width for
  // words, which is 64 bits at the time of writing.
  function automatic int get_ram_max_width(int width, int depth);
    return 0;
  endfunction

endpackage : prim_xilinx_pkg
