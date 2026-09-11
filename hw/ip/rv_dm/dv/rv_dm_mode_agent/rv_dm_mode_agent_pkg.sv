// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package rv_dm_mode_agent_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import dv_base_agent_pkg::dv_base_agent_cfg;
  import dv_base_agent_pkg::dv_base_agent;
  import dv_base_agent_pkg::dv_base_driver;
  import dv_base_agent_pkg::dv_base_monitor;
  import dv_base_agent_pkg::dv_base_sequencer;
  import dv_base_agent_pkg::dv_base_seq;

  import lc_ctrl_pkg::lc_tx_t;
  import prim_mubi_pkg::mubi4_t, prim_mubi_pkg::mubi8_t;

  `include "rv_dm_mode_agent_cfg.svh"
  `include "rv_dm_mode_seq_item.svh"
  `include "rv_dm_mode_driver.svh"
  `include "rv_dm_mode_monitor.svh"

  typedef dv_base_sequencer #(.ITEM_T(rv_dm_mode_seq_item)) rv_dm_mode_sequencer;

  `include "rv_dm_mode_agent.svh"

  `include "seq/rv_dm_mode_seq.svh"
endpackage
