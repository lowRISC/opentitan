// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package dv_lib_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import csr_utils_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // package variables
  string msg_id = "dv_lib_pkg";

  // package sources
  // base ral
  `include "dv_base_reg.sv"
  `include "dv_base_reg_field.sv"
  `include "dv_base_mem.sv"
  `include "dv_base_reg_block.sv"
  `include "dv_base_reg_map.sv"

  // base agent
  `include "dv_base_agent_cfg.sv"
  `include "dv_base_agent_cov.sv"
  `include "dv_base_monitor.sv"
  `include "dv_base_sequencer.sv"
  `include "dv_base_driver.sv"
  `include "dv_base_agent.sv"

  // base seq
  `include "dv_base_seq.sv"

  // base env
  `include "dv_base_env_cfg.sv"
  `include "dv_base_env_cov.sv"
  `include "dv_base_virtual_sequencer.sv"
  `include "dv_base_scoreboard.sv"
  `include "dv_base_env.sv"

  // base test vseq
  `include "dv_base_vseq.sv"

  // base test
  `include "dv_base_test.sv"

endpackage
