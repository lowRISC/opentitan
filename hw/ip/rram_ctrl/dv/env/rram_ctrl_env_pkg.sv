// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package rram_ctrl_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import tl_csr_agent_pkg::*;
  import tl_host_agent_pkg::*;
  import tl_prim_agent_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import rram_ctrl_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  // TODO: add the names of alerts in order
  parameter uint   NUM_ALERTS = ;
  parameter string LIST_OF_ALERTS[NUM_ALERTS] = {};

  // types

  // functions

  // package sources
  `include "rram_ctrl_env_cfg.sv"
  `include "rram_ctrl_env_cov.sv"
  `include "rram_ctrl_virtual_sequencer.sv"
  `include "rram_ctrl_scoreboard.sv"
  `include "rram_ctrl_env.sv"
  `include "rram_ctrl_vseq_list.sv"

endpackage
