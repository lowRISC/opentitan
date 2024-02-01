// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package aon_timer_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import aon_timer_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  // alerts
  parameter uint NUM_ALERTS = 1;
  parameter string LIST_OF_ALERTS[] = {"fatal_fault"};

  // types

  // functions

  // package sources
  `include "aon_timer_env_cfg.sv"
  `include "aon_timer_env_cov.sv"
  `include "aon_timer_virtual_sequencer.sv"
  `include "aon_timer_scoreboard.sv"
  `include "aon_timer_env.sv"
  `include "aon_timer_vseq_list.sv"

endpackage
