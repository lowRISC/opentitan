// Copyright 2018 lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// Core ibex environment package
// ---------------------------------------------

package core_ibex_env_pkg;

  import uvm_pkg::*;
  import ibex_mem_intf_agent_pkg::*;
  import irq_agent_pkg::*;
  import ibex_cosim_agent_pkg::*;
  import push_pull_agent_pkg::*;

  typedef push_pull_agent#(
    .DeviceDataWidth(ibex_pkg::SCRAMBLE_NONCE_W + ibex_pkg::SCRAMBLE_KEY_W)
    ) scrambling_key_agent;
  typedef push_pull_agent_cfg#(
    .DeviceDataWidth(ibex_pkg::SCRAMBLE_NONCE_W + ibex_pkg::SCRAMBLE_KEY_W)
    ) scrambling_key_agent_cfg;

  `include "core_ibex_vseqr.sv"
  `include "core_ibex_env_cfg.sv"
  `include "core_ibex_scoreboard.sv"
  `include "core_ibex_env.sv"

endpackage
