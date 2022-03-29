// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package jtag_id_pkg;

  // This is the open source facing JTAG value that should be replaced
  // by manufacturers of each OpenTitan
  localparam logic [31:0] JTAG_IDCODE = {
    4'h0,     // Version
    16'h4F54, // Part Number: "OT"
    11'h426,  // TODO: This should be replaced with Lowrisc Identity
    1'b1      // (fixed)
  };

endpackage : jtag_id_pkg
