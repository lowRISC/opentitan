// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// rv_core_ibex package
//

package rv_core_ibex_pkg;

  typedef struct packed {
    logic en;
    logic [31:0] matching_region;
    logic [31:0] remap_addr;
  } region_cfg_t;

endpackage // rv_core_ibex_pkg
