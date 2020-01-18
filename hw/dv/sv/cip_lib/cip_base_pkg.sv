// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package cip_base_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import csr_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import alert_esc_agent_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // package variables
  string msg_id = "cip_base_pkg";

  // functions

  // package sources
  // base env
  `include "cip_base_env_cfg.sv"
  `include "cip_base_env_cov.sv"
  `include "cip_base_virtual_sequencer.sv"
  `include "cip_base_scoreboard.sv"
  `include "cip_base_env.sv"

  // sequences
  `include "cip_base_vseq.sv"

  // tests
  `include "cip_base_test.sv"

endpackage
