// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package jtag_id_pkg;

  // lowRISC JEDEC Manufacturer ID, bank 13 0xEF
  localparam logic [10:0] JEDEC_MANUFACTURER_ID = {4'd12, 7'b110_1111};
  localparam logic [3:0] JTAG_VERSION = 4'h1;

  // These are the open source facing JTAG values that silicon creators may wish to replace We have
  // two TAPs, one for rv_dm and the other for lc_ctrl, they each have their own JTAG_IDCODE.  They
  // only differ in part number.

  localparam logic [31:0] RV_DM_JTAG_IDCODE = {
    JTAG_VERSION,          // Version
    16'h1,                 // Part Number
    JEDEC_MANUFACTURER_ID, // Manufacturer ID
    1'b1                   // (fixed)
  };

  localparam logic [31:0] LC_CTRL_JTAG_IDCODE = {
    JTAG_VERSION,          // Version
    16'h2,                 // Part Number
    JEDEC_MANUFACTURER_ID, // Manufacturer ID
    1'b1                   // (fixed)
  };

endpackage : jtag_id_pkg
