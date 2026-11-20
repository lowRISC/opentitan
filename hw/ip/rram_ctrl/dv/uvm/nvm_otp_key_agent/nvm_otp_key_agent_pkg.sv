// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package nvm_otp_key_agent_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import dv_base_agent_pkg::dv_base_agent_cfg;
  import dv_base_agent_pkg::dv_base_driver;
  import dv_base_agent_pkg::dv_base_monitor;
  import dv_base_agent_pkg::dv_base_sequencer;
  import dv_base_agent_pkg::dv_base_agent;

  import otp_ctrl_pkg::NvmKeyWidth;

  // The number of cycles that an active agent will hold a key value stable after acknowledging a
  // key request.
  //
  // This time is dictated by the interfaces.md document of the otp_ctrl specification (the block
  // that this agent would be impersonating).
  parameter int unsigned KeyStabilityCycles = 62;

  `include "nvm_otp_key_agent_cfg.svh"
  `include "nvm_otp_key_req_seq_item.svh"
  `include "nvm_otp_key_rsp_seq_item.svh"
  `include "nvm_otp_key_rsp_drive_seq_item.svh"
  `include "nvm_otp_key_driver.svh"
  `include "nvm_otp_key_monitor.svh"
  `include "nvm_otp_key_sequencer.svh"

  `include "seq/nvm_otp_key_seq.svh"

  `include "nvm_otp_key_agent.svh"
endpackage
