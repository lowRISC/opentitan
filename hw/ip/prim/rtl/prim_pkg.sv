// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Constants for use in primitives

package prim_pkg;

  // Implementation target specialization
  typedef enum integer {
    ImplGeneric = 0,
    ImplXilinx  = 1
  } impl_e;

endpackage : prim_pkg
