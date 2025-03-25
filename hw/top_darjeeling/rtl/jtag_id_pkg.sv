// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package jtag_id_pkg;

  // lowRISC JEDEC Manufacturer ID, bank 13 0xEF
  localparam logic [10:0] JEDEC_MANUFACTURER_ID = {4'd12, 7'b110_1111};
  localparam logic [3:0] JTAG_VERSION = 4'h1;
  localparam logic [11:0] PART_TYPE = 12'h1;

  // These are the open source facing JTAG values that silicon creators may wish to replace.
  // We have three TAPs, one for rv_dm, one for lc_ctrl and one combined TAP.
  // They each have their own JTAG_IDCODE where they differ in the TAP type of
  // the part number.

  localparam logic [31:0] RV_DM_JTAG_IDCODE = {
    JTAG_VERSION,          // Version
                           // Part Number:
    PART_TYPE,             // - Part Type
    4'h1,                  // - TAP Type
    JEDEC_MANUFACTURER_ID, // Manufacturer ID
    1'b1                   // (fixed)
  };

  localparam logic [31:0] LC_CTRL_JTAG_IDCODE = {
    JTAG_VERSION,          // Version
                           // Part Number:
    PART_TYPE,             // - Part Type
    4'h2,                  // - TAP Type
    JEDEC_MANUFACTURER_ID, // Manufacturer ID
    1'b1                   // (fixed)
  };

  localparam logic [31:0] LC_DM_COMBINED_JTAG_IDCODE = {
    JTAG_VERSION,          // Version
                           // Part Number:
    PART_TYPE,             // - Part Type
    4'h3,                  // - TAP Type
    JEDEC_MANUFACTURER_ID, // Manufacturer ID
    1'b1                   // (fixed)
  };

endpackage : jtag_id_pkg
