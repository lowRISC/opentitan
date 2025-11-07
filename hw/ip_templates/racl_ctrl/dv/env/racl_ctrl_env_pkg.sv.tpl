// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ${module_instance_name}_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import dv_base_reg_pkg::*;
  import csr_utils_pkg::*;
  import ${module_instance_name}_ral_pkg::*;

  import racl_error_log_agent_pkg::racl_error_log_agent;
  import racl_error_log_agent_pkg::racl_error_log_agent_cfg;
  import racl_error_log_agent_pkg::racl_error_log_sequencer;
  import racl_error_log_agent_pkg::racl_error_log_item;
  import racl_error_log_agent_pkg::racl_error_log_vec_item;
  import racl_error_log_agent_pkg::racl_error_log_sporadic_seq;

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
  `include "racl_ctrl_env_wrapper_cfg.sv"
  `include "${module_instance_name}_env_cfg.sv"
  `include "${module_instance_name}_env_cov.sv"
  `include "${module_instance_name}_virtual_sequencer.sv"
  `include "${module_instance_name}_error_arb_predictor.sv"
  `include "${module_instance_name}_scoreboard.sv"
  `include "${module_instance_name}_env.sv"
  `include "${module_instance_name}_vseq_list.sv"

endpackage
