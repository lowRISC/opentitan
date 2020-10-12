// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package sw_test_status_pkg;

  // Enum to indicate the SW test status.
  typedef enum bit [15:0] {
    SwTestStatusUnderReset  = 16'h0000, // 'boot', CPU is under reset.
    SwTestStatusBooted      = 16'hb004, // 'boot', CPU has booted.
    SwTestStatusInBootRom   = 16'hb090, // 'bogo', BOotrom GO, SW has entered the boot rom code.
    SwTestStatusInTest      = 16'h4354, // 'test', SW has entered the test code.
    SwTestStatusInWfi       = 16'h1d1e, // 'idle', CPU has entered WFI state.
    SwTestStatusPassed      = 16'h900d, // 'good', SW test has passed.
    SwTestStatusFailed      = 16'hbaad  // 'baad', SW test has failed.
  } sw_test_status_e;

endpackage
