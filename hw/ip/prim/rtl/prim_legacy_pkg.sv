// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Legacy constants that were used in some IPs
// These are deprecated and should be removed.

package prim_pkg;

  // Implementation target specialization
  typedef enum integer {
    ImplGeneric,
    ImplXilinx,
    ImplBadbit,
    ImplXilinx_ultrascale
  } impl_e;

  `ifndef PRIM_DEFAULT_IMPL
    `define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
  `endif

endpackage : prim_pkg
