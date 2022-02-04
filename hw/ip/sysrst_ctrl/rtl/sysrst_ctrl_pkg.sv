// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package sysrst_ctrl_pkg;

  typedef enum logic [1:0] {
    LowLevel,
    HighLevel,
    EdgeToLow,
    EdgeToHigh
  } event_t;

endpackage : sysrst_ctrl_pkg
