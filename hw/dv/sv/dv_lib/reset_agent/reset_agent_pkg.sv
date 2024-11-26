// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package reset_agent_pkg;
  // Dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_base_agent_pkg::*;

  // Macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // Typedefs
  typedef enum bit {ActiveHigh=0, ActiveLow=1} polarity_e;
  typedef enum bit {Deassertion=0, Assertion=1} reset_phase_e;
  typedef enum bit {ResetDeasserted=0, ResetAsserted=1} reset_state_e;

  // // Package variables
  // string msg_id = "reset_agent_pkg";

  // Package sources
  `include "reset_item.svh"
  `include "reset_agent_cfg.svh"
  `include "reset_agent_cov.svh"
  `include "reset_sequencer.svh"
  `include "reset_driver.svh"
  `include "reset_monitor.svh"
  `include "reset_agent.svh"
  `include "seq_lib/reset_seq_lib.sv"
endpackage : reset_agent_pkg
