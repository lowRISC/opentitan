// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Target-side hardware extension.
package i3c_targ_ext_pkg;
  // This is a placeholder for the Target-side extension.
  //
  // These structures provide access to the register interface in `i3c_core` without
  // necessarily requiring modification of the intervening module hierarchy.

  // Register interface to target extension.
  typedef struct packed {
    bit dummy;
  } i3c_reg2targ_ext_t;

  // Target extension to register interface.
  typedef struct packed {
    bit dummy;
  } i3c_targ_ext2reg_t;

endpackage
