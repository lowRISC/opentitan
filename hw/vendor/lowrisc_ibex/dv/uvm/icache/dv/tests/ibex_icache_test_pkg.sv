// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ibex_icache_test_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_lib_pkg::*;
  import ibex_icache_env_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // local types

  // functions

  // package sources
  `include "ibex_icache_base_test.sv"
  `include "ibex_icache_oldval_test.sv"

endpackage
