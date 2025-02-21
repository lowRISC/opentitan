// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ac_range_check_env_pkg;
  // Dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import tl_agent_pkg::*;
  import dv_lib_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import ac_range_check_ral_pkg::*;

  // Macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // Parameters
  parameter uint   NUM_ALERTS = 2;
  parameter string LIST_OF_ALERTS[] = {"recov_ctrl_update_err", "fatal_fault"};

  // Types
  typedef enum int {
    DenyCntReached = 0
  } ac_range_check_intr_e;

  // Functions

  // Package sources
  `include "ac_range_check_env_cfg.sv"
  `include "ac_range_check_env_cov.sv"
  `include "ac_range_check_virtual_sequencer.sv"
  `include "ac_range_check_scoreboard.sv"
  `include "ac_range_check_env.sv"
  `include "ac_range_check_vseq_list.sv"
endpackage : ac_range_check_env_pkg
