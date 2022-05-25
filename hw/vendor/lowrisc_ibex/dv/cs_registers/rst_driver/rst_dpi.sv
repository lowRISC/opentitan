// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package rst_dpi;

  import "DPI-C"
  function void rst_tick (
    input  string     name,
    output bit        rst_n);

endpackage
