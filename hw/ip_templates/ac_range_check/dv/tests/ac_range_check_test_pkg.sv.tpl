// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ${module_instance_name}_test_pkg;
  // Dep packages
  import uvm_pkg::*;
  import cip_base_pkg::*;
  import ${module_instance_name}_env_pkg::*;

  // Macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // Local types

  // Functions

  // Package sources
  `include "${module_instance_name}_base_test.sv"

endpackage
