// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ${name}_test_pkg;
  // dep packages
  import uvm_pkg::*;
% if is_cip:
  import cip_base_pkg::*;
% else:
  import dv_lib_pkg::*;
% endif
  import ${name}_env_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // local types

  // functions

  // package sources
  `include "${name}_base_test.sv"

endpackage
