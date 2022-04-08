// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package pwrmgr_clk_ctrl_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter uint MAIN_CLK_DELAY_MIN = 15;  // cycle of aon clk
  parameter uint MAIN_CLK_DELAY_MAX = 258; // cycle of aon clk
  parameter uint ESC_CLK_DELAY_MIN = 1;    // cycle of aon clk
  parameter uint ESC_CLK_DELAY_MAX = 10;   // cycle of aon clk
  // local types
  // forward declare classes to allow typedefs below
  typedef class pwrmgr_clk_ctrl_item;
  typedef class pwrmgr_clk_ctrl_agent_cfg;

  // reuse dv_base_sequencer as is with the right parameter set
  typedef dv_base_sequencer #(.ITEM_T(pwrmgr_clk_ctrl_item),
                              .CFG_T (pwrmgr_clk_ctrl_agent_cfg)) pwrmgr_clk_ctrl_sequencer;

  // functions

  // package sources
  `include "pwrmgr_clk_ctrl_item.sv"
  `include "pwrmgr_clk_ctrl_agent_cfg.sv"
  `include "pwrmgr_clk_ctrl_agent_cov.sv"
  `include "pwrmgr_clk_ctrl_driver.sv"
  `include "pwrmgr_clk_ctrl_monitor.sv"
  `include "pwrmgr_clk_ctrl_agent.sv"
  `include "pwrmgr_clk_ctrl_seq_list.sv"

endpackage: pwrmgr_clk_ctrl_agent_pkg
