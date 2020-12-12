// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package aes_test_pkg;
  // dep packages
  import uvm_pkg::*;
  import cip_base_pkg::*;
  import aes_env_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // local types

  // functions

  // package sources
  `include "aes_base_test.sv"
  `include "aes_wake_up_test.sv"
  `include "aes_smoke_test.sv"
  `include "aes_stress_test.sv"
  `include "aes_b2b_test.sv"
  `include "aes_config_error_test.sv"
  `include "aes_clear_test.sv"

endpackage
