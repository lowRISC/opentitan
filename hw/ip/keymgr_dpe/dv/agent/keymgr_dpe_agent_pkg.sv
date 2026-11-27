// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package keymgr_dpe_agent_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import keymgr_dpe_pkg::*;
  import lc_ctrl_pkg::lc_tx_t;
  import lc_ctrl_pkg::lc_keymgr_div_t;
  import rom_ctrl_pkg::keymgr_data_t;

  import dv_base_agent_pkg::dv_base_agent_cfg;
  import dv_base_agent_pkg::dv_base_agent;
  import dv_base_agent_pkg::dv_base_driver;
  import dv_base_agent_pkg::dv_base_monitor;
  import dv_base_agent_pkg::dv_base_sequencer;
  import dv_base_agent_pkg::dv_base_seq;

  parameter int unsigned NUM_ROM_DIGESTS = 1;

  typedef class keymgr_dpe_agent_cfg;
  typedef class keymgr_dpe_agent;
  typedef class keymgr_dpe_driver;
  typedef class keymgr_dpe_monitor;
  typedef class keymgr_dpe_seq_item;
  typedef class keymgr_dpe_base_seq;
  typedef dv_base_sequencer #(.ITEM_T(keymgr_dpe_seq_item)) keymgr_dpe_sequencer;

  `include "keymgr_dpe_agent_cfg.sv"
  `include "keymgr_dpe_agent.sv"
  `include "keymgr_dpe_driver.sv"
  `include "keymgr_dpe_monitor.sv"
  `include "keymgr_dpe_seq_item.sv"
  `include "seq/keymgr_dpe_base_seq.sv"
endpackage
