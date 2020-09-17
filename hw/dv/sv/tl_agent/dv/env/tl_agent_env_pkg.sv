// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// tl_agent environment package
// ---------------------------------------------
package tl_agent_env_pkg;

  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import tl_agent_pkg::*;
  import dv_lib_pkg::*;

  typedef class tl_agent_env_cfg;
  typedef dv_base_env_cov #(.CFG_T(tl_agent_env_cfg)) tl_agent_env_cov;

  `include "tl_agent_env_cfg.sv"
  `include "tl_agent_virtual_sequencer.sv"
  `include "tl_agent_scoreboard.sv"
  `include "tl_agent_env.sv"
  `include "tl_agent_vseq_list.sv"

endpackage
