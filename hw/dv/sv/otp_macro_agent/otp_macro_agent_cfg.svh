// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Configuration class for otp_macro_agent

class otp_macro_agent_cfg extends dv_base_agent_cfg;
  `uvm_object_utils(otp_macro_agent_cfg)

  virtual otp_macro_if m_vif;

  extern function new (string name="");
endclass

function otp_macro_agent_cfg::new (string name="");
  super.new(name);

  // The default value in dv_base_agent_cfg is that is_active=1. An active interface for this agent
  // only makes sense with if_mode = Host, where the agent acts as otp_ctrl.
  if_mode = dv_utils_pkg::Host;
endfunction
