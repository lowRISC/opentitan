// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package rv_timer_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import csr_utils_pkg::*;
  import tl_agent_pkg::*;
  import dv_lib_pkg::*;
  import cip_base_pkg::*;
  import rv_timer_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // local parameters and types
  // These are currently hardcoded to 1 - this will need to change if design is modified
  parameter uint NUM_HARTS = 1;
  parameter uint NUM_TIMERS = 1;

  typedef class rv_timer_env_cfg;
  typedef class rv_timer_env_cov;
  typedef cip_base_virtual_sequencer #(rv_timer_env_cfg,
                                       rv_timer_env_cov) rv_timer_virtual_sequencer;

  // functions

  // package sources
  `include "rv_timer_env_cfg.sv"
  `include "rv_timer_env_cov.sv"
  `include "rv_timer_scoreboard.sv"
  `include "rv_timer_env.sv"
  `include "rv_timer_vseq_list.sv"
endpackage
