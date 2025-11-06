// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package rram_ctrl_env_pkg;
  // Dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import tl_agent_pkg::*;
  import dv_lib_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import rram_ctrl_pkg::*;
  import rram_ctrl_core_ral_pkg::*;
  import rram_ctrl_host_ral_pkg::*;
  import rram_ctrl_prim_ral_pkg::*;

  // Macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // Parameters
  parameter uint   NUM_ALERTS = 5;
  parameter string LIST_OF_ALERTS[NUM_ALERTS] = {
    "recov_err",
    "fatal_std_err",
    "fatal_err",
    "fatal_prim_rram_alert",
    "recov_prim_rram_alert"
  };

  // Types
  typedef virtual rram_ctrl_misc_io_if misc_vif_t;

  typedef enum bit [1:0] {
    AddrRead  = 0,
    AddrWrite = 1,
    DataRead  = 2,
    DataWrite = 3
  } tl_phase_e;

  // Functions

  // Package sources
  `include "rram_ctrl_env_cfg.sv"
  `include "rram_ctrl_env_cov.sv"
  `include "rram_ctrl_virtual_sequencer.sv"
  `include "rram_ctrl_scoreboard.sv"
  `include "rram_ctrl_env.sv"
  `include "rram_ctrl_vseq_list.sv"
endpackage : rram_ctrl_env_pkg
