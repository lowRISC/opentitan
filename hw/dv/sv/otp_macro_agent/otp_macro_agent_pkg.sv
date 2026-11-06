// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package otp_macro_agent_pkg;
  // Dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_base_agent_pkg::*;
  import otp_ctrl_macro_pkg::*;

  // Macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // Number of OTP words (each OtpWidth bits) that one request can carry.
  parameter int unsigned OtpMacroMaxWords = 2 ** OtpSizeWidth;

  // Package sources
  `include "otp_macro_item.sv"
  `include "otp_macro_agent_cfg.sv"
  `include "otp_macro_monitor.sv"
  `include "otp_macro_sequencer.sv"
  `include "otp_macro_host_driver.sv"
  `include "otp_macro_seq_list.sv"
  `include "otp_macro_agent.sv"
endpackage : otp_macro_agent_pkg
