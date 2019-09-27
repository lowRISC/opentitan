// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ${name}_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import csr_utils_pkg::*;
  import tl_agent_pkg::*;
% for agent in env_agents:
  import ${agent}_agent_pkg::*;
% endfor
  import dv_lib_pkg::*;
% if is_cip:
  import cip_base_pkg::*;
% endif

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  // TODO update below, or compile error occurs
  parameter uint ADDR_MAP_SIZE   = ;

  // types
% if env_agents == []:
  // forward declare classes to allow typedefs below
  typedef class ${name}_env_cfg;
  typedef class ${name}_env_cov;

% endif
% if env_agents == [] and is_cip:
  // reuse cip_base_virtual_seqeuencer as is with the right parameter set
  typedef class cip_base_virtual_sequencer #(
% elif env_agents == [] and not is_cip:
  // reuse dv_base_virtual_seqeuencer as is with the right parameter set
  typedef class dv_base_virtual_sequencer #(
% endif
% if env_agents == []:
      .CFG_T(${name}_env_cfg),
      .COV_T(${name}_env_cov)
  ) ${name}_virtual_sequencer;
% endif

  // functions

  // package sources
  `include "${name}_reg_block.sv"
  `include "${name}_env_cfg.sv"
  `include "${name}_env_cov.sv"
% if env_agents != []:
  `include "${name}_virtual_sequencer.sv"
% endif
  `include "${name}_scoreboard.sv"
  `include "${name}_env.sv"
  `include "${name}_vseq_list.sv"

endpackage
