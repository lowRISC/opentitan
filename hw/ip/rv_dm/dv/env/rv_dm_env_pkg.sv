// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package rv_dm_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import bus_params_pkg::*;
  import jtag_agent_pkg::*;
  import jtag_dmi_agent_pkg::*;
  import jtag_rv_debugger_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import rv_dm_regs_ral_pkg::*;
  import rv_dm_mem_ral_pkg::*;
  import rv_dm_reg_pkg::NrHarts;
  import rv_dm_reg_pkg::NumAlerts;
  import dm::*;
  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter uint NUM_HARTS = rv_dm_reg_pkg::NrHarts;
  parameter uint RV_DM_JTAG_IDCODE = `BUILD_SEED;

  // Design uses 5 bits for IR.
  parameter uint JTAG_IR_LEN = 5;

  // See hw/ip/rm_dm/data/rv_dm.hjson for alert names.
  parameter uint NUM_ALERTS = rv_dm_reg_pkg::NumAlerts;
  parameter string LIST_OF_ALERTS[] = {"fatal_fault"};

  // package sources
  `include "rv_dm_env_cfg.sv"
  `include "rv_dm_env_cov.sv"
  `include "rv_dm_virtual_sequencer.sv"
  `include "rv_dm_scoreboard.sv"
  `include "rv_dm_env.sv"
  `include "rv_dm_vseq_list.sv"

endpackage
