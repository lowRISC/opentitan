// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// xBar test package
// ---------------------------------------------
package xbar_test_pkg;

  import uvm_pkg::*;
  import xbar_env_pkg::*;
  import tl_agent_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;

  `include "xbar_base_test.sv"
  `include "xbar_error_test.sv"

endpackage
