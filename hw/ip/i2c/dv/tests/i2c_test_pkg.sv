// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package i2c_test_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import cip_base_pkg::*;
  import i2c_env_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // local types

  // functions

  // package sources
  `include "i2c_base_test.sv"

endpackage
