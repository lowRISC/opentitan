// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package alert_handler_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import csr_utils_pkg::*;
  import tl_agent_pkg::*;
  import alert_esc_agent_pkg::*;
  import dv_lib_pkg::*;
  import cip_base_pkg::*;
  import alert_handler_ral_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter uint ALERT_HANDLER_ADDR_MAP_SIZE = 2048;
  parameter uint NUM_MAX_ESC_SEV             = 8;
  parameter uint NUM_ALERT_HANDLER_CLASSES   = 4;

  // types
  // forward declare classes to allow typedefs below
  typedef virtual pins_if #(NUM_MAX_ESC_SEV) esc_en_vif;
  typedef virtual pins_if #(1) entropy_vif;

  // functions

  // package sources
  `include "alert_handler_env_cfg.sv"
  `include "alert_handler_env_cov.sv"
  `include "alert_handler_virtual_sequencer.sv"
  `include "alert_handler_scoreboard.sv"
  `include "alert_handler_env.sv"
  `include "alert_handler_vseq_list.sv"

endpackage
