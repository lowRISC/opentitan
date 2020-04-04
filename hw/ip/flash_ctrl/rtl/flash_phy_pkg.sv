// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Flash phy module package
//

package flash_phy_pkg;

  // Flash Operations Supported
  typedef enum logic [2:0] {
    PhyRead      = 3'h0,
    PhyProg      = 3'h1,
    PhyPgErase   = 3'h2,
    PhyBkErase   = 3'h3,
    PhyOps       = 3'h4
  } flash_phy_op_e;

  // Flash Operations Selected
  typedef enum logic [1:0] {
    None         = 2'h0,
    Host         = 2'h1,
    Ctrl         = 2'h2
  } flash_phy_op_sel_e;


endpackage // flash_phy_pkg
