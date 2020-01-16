// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usb20_agent_cov extends dv_base_agent_cov #(usb20_agent_cfg);
  `uvm_component_utils(usb20_agent_cov)

  // the base class provides the following handles for use:
  // usb20_agent_cfg: cfg

  // covergroups

  function new(string name, uvm_component parent);
    super.new(name, parent);
    // instantiate all covergroups here
  endfunction : new

endclass
