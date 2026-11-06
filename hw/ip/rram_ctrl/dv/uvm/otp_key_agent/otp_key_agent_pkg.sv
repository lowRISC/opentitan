// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package otp_key_agent_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import dv_base_agent_pkg::dv_base_agent_cfg;
  import dv_base_agent_pkg::dv_base_driver;
  import dv_base_agent_pkg::dv_base_monitor;
  import dv_base_agent_pkg::dv_base_sequencer;
  import dv_base_agent_pkg::dv_base_agent;

  import otp_ctrl_pkg::NvmKeyWidth;

  `include "otp_key_agent_cfg.svh"
  `include "otp_key_req_seq_item.svh"
  `include "otp_key_rsp_seq_item.svh"
  `include "otp_key_driver.svh"
  `include "otp_key_monitor.svh"
  `include "otp_key_sequencer.svh"

  `include "seq/otp_key_seq.svh"

  `include "otp_key_agent.svh"
endpackage
