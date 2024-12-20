// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package dv_lib_pkg;
  // dep packages
  import uvm_pkg::*;
  import bus_params_pkg::*;
  import dv_utils_pkg::*;
  import csr_utils_pkg::*;
  import dv_base_reg_pkg::*;
  // import dv_base_agent_pkg::*;
  // import reset_agent_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // package variables
  string msg_id = "dv_lib_pkg";

  // Typedefs
  typedef enum bit {ActiveHigh=0, ActiveLow=1} polarity_e;
  typedef enum bit {Deassertion=0, Assertion=1} reset_phase_e;
  typedef enum bit {ResetDeasserted=0, ResetAsserted=1} reset_state_e;

  // package sources
  // base agent
  `include "dv_base_agent_cfg.sv"
  `include "dv_base_agent_cov.sv"
  `include "dv_base_monitor.sv"
  `include "dv_base_sequencer.sv"
  `include "dv_base_driver.sv"
  `include "dv_base_agent.sv"
  `include "dv_base_seq.sv"

  // reset agent
  `include "reset_item.svh"
  `include "reset_agent_cfg.svh"
  `include "reset_agent_cov.svh"
  `include "reset_sequencer.svh"
  `include "reset_driver.svh"
  `include "reset_monitor.svh"
  `include "reset_agent.svh"
  `include "seq_lib/reset_seq_lib.sv"

  // base env
  `include "dv_base_env_cfg.sv"
  `include "dv_base_env_cov.sv"
  `include "dv_base_virtual_sequencer.sv"
  `include "dv_base_scoreboard.sv"
  `include "dv_base_env.sv"

  // base test vseq
  `include "dv_base_vseq.sv"

  // base test
  `include "dv_base_test.sv"

endpackage
