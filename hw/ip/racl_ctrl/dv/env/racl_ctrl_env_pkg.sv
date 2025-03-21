// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package racl_ctrl_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import racl_ctrl_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // The LIST_OF_ALERTS string gives a list of alert names, used by the environment config (through
  // cip_base_env_cfg) to instantiate agents for handling alerts.
  //
  // The connection to the dut is done through interfaces that are put in the config_db in the
  // (templated) tb.sv. For this to work, every alert in this list must also be listed in tb.sv.
  string LIST_OF_ALERTS[2] = {"fatal_fault", "recov_ctrl_update_err"};

  localparam int unsigned PolicyBits = $bits(top_racl_pkg::racl_policy_vec_t);

  // package sources
  `include "racl_ctrl_reg_window.sv"
  `include "racl_ctrl_env_cfg.sv"
  `include "racl_ctrl_env_cov.sv"
  `include "racl_ctrl_virtual_sequencer.sv"
  `include "racl_ctrl_scoreboard.sv"
  `include "racl_ctrl_env.sv"
  `include "racl_ctrl_vseq_list.sv"

endpackage
