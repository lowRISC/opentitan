// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package csrng_test_pkg;
  // dep packages
  import uvm_pkg::*;
  import cip_base_pkg::*;
  import csrng_env_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // package sources
  `include "csrng_base_test.sv"
  `include "csrng_smoke_test.sv"
  `include "csrng_cmds_test.sv"
  `include "csrng_stress_all_test.sv"
  `include "csrng_intr_test.sv"
  `include "csrng_alert_test.sv"
  `include "csrng_regwen_test.sv"

endpackage
