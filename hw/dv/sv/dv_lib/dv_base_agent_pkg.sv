// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package dv_base_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // package variables
  string msg_id = "dv_base_agent_pkg";

  // package sources
  `include "dv_base_agent_cfg.sv"
  `include "dv_base_agent_cov.sv"
  `include "dv_base_monitor.sv"
  `include "dv_base_sequencer.sv"
  `include "dv_base_driver.sv"
  `include "dv_base_agent.sv"

  // base seq
  `include "dv_base_seq.sv"

endpackage
