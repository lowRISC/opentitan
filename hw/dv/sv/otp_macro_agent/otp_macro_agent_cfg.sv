// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otp_macro_agent_cfg extends dv_base_agent_cfg;

  virtual otp_macro_if vif;

  // How long the driver waits for a response before giving up with an error. Init can take a
  // while, because the responder only answers once its own memory has finished initializing.
  int unsigned rsp_timeout_ns = 1_000_000;

  `uvm_object_utils_begin(otp_macro_agent_cfg)
    `uvm_field_int(rsp_timeout_ns, UVM_DEFAULT | UVM_DEC)
  `uvm_object_utils_end

  extern function new(string name = "");
endclass : otp_macro_agent_cfg

function otp_macro_agent_cfg::new(string name = "");
  super.new(name);
  // The agent plays otp_ctrl, which starts every transaction.
  if_mode = Host;
endfunction : new
