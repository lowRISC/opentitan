// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package rram_macro_agent_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import dv_base_agent_pkg::dv_base_agent_cfg;
  import dv_base_agent_pkg::dv_base_monitor;
  import dv_base_agent_pkg::dv_base_agent;

  import rram_ctrl_pkg::rram_part_e;
  import rram_ctrl_pkg::AddrW;
  import rram_ctrl_pkg::DataWidth;

  `include "rram_macro_agent_cfg.svh"
  `include "rram_macro_req_seq_item.svh"
  `include "rram_macro_rsp_seq_item.svh"
  `include "rram_macro_monitor.svh"

  `include "rram_macro_agent.svh"
endpackage
