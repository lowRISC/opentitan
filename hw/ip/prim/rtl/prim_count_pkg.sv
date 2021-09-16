// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Package for primitive hardened counter module
//

package prim_count_pkg;

  // Enumeration for hardened count style
  typedef enum logic {
    CrossCnt, // up count and down count
    DupCnt    // duplicate counters
  } prim_count_style_e;

  // Enumeration for differential valid
  typedef enum logic [1:0] {
    CmpInvalid = 2'b01,
    CmpValid   = 2'b10
  } cmp_valid_e;

endpackage //
