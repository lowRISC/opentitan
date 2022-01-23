// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package entropy_src_test_pkg;
  // dep packages
  import uvm_pkg::*;
  import cip_base_pkg::*;
  import entropy_src_env_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // package sources
  `include "entropy_src_base_test.sv"
  `include "entropy_src_smoke_test.sv"
  `include "entropy_src_rng_test.sv"
  `include "entropy_src_fw_ov_test.sv"
  `include "entropy_src_stress_all_test.sv"

endpackage
