// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package dv_seq_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_lib_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // package variables
  string msg_id = "dv_seq_agent_pkg";

  // package sources
  `include "dv_seq_agent_cfg.sv"
  `include "dv_seq_monitor.sv"
  `include "dv_seq_sequencer.sv"
  `include "dv_seq_agent.sv"

endpackage
