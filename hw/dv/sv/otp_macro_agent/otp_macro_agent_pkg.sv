// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package otp_macro_agent_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import dv_base_agent_pkg::dv_base_agent_cfg;
  import dv_base_agent_pkg::dv_base_driver;
  import dv_base_agent_pkg::dv_base_monitor;
  import dv_base_agent_pkg::dv_base_sequencer;
  import dv_base_agent_pkg::dv_base_seq;
  import dv_base_agent_pkg::dv_base_agent;

  // The types, sizes and the command and error encodings of the OTP macro interface.
  import otp_ctrl_macro_pkg::*;

  // Number of OTP words (each OtpWidth bits) that one request can carry.
  parameter int unsigned OtpMacroMaxWords = 2 ** OtpSizeWidth;

  `include "otp_macro_agent_cfg.svh"
  `include "otp_macro_req_seq_item.svh"
  `include "otp_macro_rsp_seq_item.svh"
  `include "otp_macro_driver.svh"
  `include "otp_macro_monitor.svh"

  // The agent's sequencer needs nothing beyond the base class.
  typedef dv_base_sequencer #(.ITEM_T     (otp_macro_req_seq_item),
                              .CFG_T      (otp_macro_agent_cfg),
                              .RSP_ITEM_T (otp_macro_rsp_seq_item)) otp_macro_sequencer;

  `include "seq/otp_macro_cmd_seq.svh"

  `include "otp_macro_agent.svh"
endpackage
