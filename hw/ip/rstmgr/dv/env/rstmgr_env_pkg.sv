// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package rstmgr_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import rstmgr_ral_pkg::*;

  import prim_mubi_pkg::mubi4_t;
  import prim_mubi_pkg::MuBi4False;
  import prim_mubi_pkg::MuBi4True;

  import rstmgr_reg_pkg::NumHwResets;
  import rstmgr_reg_pkg::NumSwResets;

  import alert_pkg::alert_crashdump_t;
  import rv_core_ibex_pkg::cpu_crash_dump_t;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  // TODO: add the names of alerts in order
  parameter string LIST_OF_ALERTS[] = {"fatal_fault", "fatal_cnsty_fault"};
  parameter uint NUM_ALERTS = 2;

  // types
  typedef logic [NumSwResets-1:0] sw_rst_t;

  typedef logic [$bits(alert_crashdump_t)-1:0] linearized_alert_dump_t;

  // functions

  // package sources
  `include "rstmgr_env_cfg.sv"
  `include "rstmgr_env_cov.sv"
  `include "rstmgr_virtual_sequencer.sv"
  `include "rstmgr_scoreboard.sv"
  `include "rstmgr_env.sv"
  `include "rstmgr_vseq_list.sv"

endpackage
