// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Constants for use in primitives

// This file is auto-generated.

package prim_pkg;

  // Implementation target specialization
  typedef enum integer {
    ${',\n    '.join(techlib_enums)}
  } impl_e;
endpackage : prim_pkg
