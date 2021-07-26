// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package prim_subreg_pkg;

  // Register access specifier
  typedef enum logic [2:0] {
    SwAccessRW  = 3'd0, // Read-write
    SwAccessRO  = 3'd1, // Read-only
    SwAccessWO  = 3'd2, // Write-only
    SwAccessW1C = 3'd3, // Write 1 to clear
    SwAccessW1S = 3'd4, // Write 1 to set
    SwAccessW0C = 3'd5, // Write 0 to clear
    SwAccessRC  = 3'd6  // Read to clear. Do not use, only exists for compatibility.
  } sw_access_e;
endpackage
