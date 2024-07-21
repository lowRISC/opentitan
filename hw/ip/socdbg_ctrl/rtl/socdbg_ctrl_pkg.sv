// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package socdbg_ctrl_pkg;


  ////////////////////////
  // General Parameters //
  ////////////////////////

  ////////////////////////
  // Defined Structures
  ////////////////////////
  typedef struct packed {
      logic [2:0]   policy;
      logic         valid;
  } soc_dbg_policy_t;

endpackage : socdbg_ctrl_pkg
