// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package prim_rom_pkg;

  typedef struct packed {
    logic       cfg_en;
    logic [3:0] cfg;
  } rom_cfg_t;

  parameter rom_cfg_t ROM_CFG_DEFAULT = '0;

endpackage // prim_rom_pkg
