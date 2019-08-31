// Copyright 2018 lowRISC contributors.
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

  `include "xbar_seq_lib.sv"
  `include "xbar_vseq.sv"
  `include "xbar_base_test.sv"

endpackage
