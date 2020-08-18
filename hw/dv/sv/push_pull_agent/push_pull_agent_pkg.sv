// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package push_pull_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // Instantiated in agent's config object.
  typedef enum {
    PushAgent,
    PullAgent
  } push_pull_agent_e;

  `include "push_pull_item.sv"
  `include "push_pull_agent_cfg.sv"
  `include "push_pull_agent_cov.sv"
  `include "push_pull_driver.sv"
  `include "push_pull_host_driver.sv"
  `include "push_pull_device_driver.sv"
  `include "push_pull_monitor.sv"
  `include "push_pull_sequencer.sv"
  `include "push_pull_seq_list.sv"
  `include "push_pull_agent.sv"

endpackage: push_pull_agent_pkg
