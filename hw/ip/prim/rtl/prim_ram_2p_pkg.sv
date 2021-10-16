// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package prim_ram_2p_pkg;

  typedef struct packed {
    logic       cfg_en;
    logic [3:0] cfg;
  } cfg_t;

  typedef struct packed {
    cfg_t a_ram_fcfg;  // configuration for a port
    cfg_t b_ram_fcfg;  // configuration for b port
    cfg_t a_ram_lcfg;  // configuration for a port
    cfg_t b_ram_lcfg;  // configuration for b port
  } ram_2p_cfg_t;

  parameter ram_2p_cfg_t RAM_2P_CFG_DEFAULT = '0;

endpackage // prim_ram_2p_pkg
