// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class racl_error_log_agent_cfg extends dv_base_agent_cfg;

  `uvm_object_utils(racl_error_log_agent_cfg)

  // This is the number of subscribing IPs that can log errors. It can be recovered from the
  // parameters passed to racl_ctrl by looking at NumSubscribingIps or NumExternalSubscribingIps.
  //
  // The class variable defaults to zero (which means error logs won't have any errors!) but a
  // testbench will probably want to supply a sensible value.
  int unsigned num_subscribing_ips;

  virtual racl_error_log_if vif;

  extern function new (string name="");
endclass

function racl_error_log_agent_cfg::new(string name="");
  super.new(name);
endfunction
