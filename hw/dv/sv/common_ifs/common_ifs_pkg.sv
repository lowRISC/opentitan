// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package common_ifs_pkg;
  // dep packages
  import uvm_pkg::*;

  // Enum representing reset scheme
  typedef enum bit [1:0] {
    RstAssertSyncDeassertSync,
    RstAssertAsyncDeassertSync,
    RstAssertAsyncDeassertASync
  } rst_scheme_e;
endpackage
