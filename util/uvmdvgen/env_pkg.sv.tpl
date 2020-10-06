// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ${name}_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
% for agent in env_agents:
  import ${agent}_agent_pkg::*;
% endfor
  import dv_lib_pkg::*;
% if is_cip:
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
% endif
% if has_ral:
  import csr_utils_pkg::*;
  import ${name}_ral_pkg::*;
% endif

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
% if has_alerts:
  // TODO: add the names of alerts in order
  parameter string LIST_OF_ALERTS[] = {};
  parameter uint   NUM_ALERTS = ;
% endif

  // types
% if not has_ral:
  typedef dv_base_reg_block ${name}_reg_block;
% endif

  // functions

  // package sources
  `include "${name}_env_cfg.sv"
  `include "${name}_env_cov.sv"
  `include "${name}_virtual_sequencer.sv"
  `include "${name}_scoreboard.sv"
  `include "${name}_env.sv"
  `include "${name}_vseq_list.sv"

endpackage
