// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class push_pull_agent_cov #(parameter int HostDataWidth = 32,
                            parameter int DeviceDataWidth = HostDataWidth)
  extends dv_base_agent_cov #(
    push_pull_agent_cfg#(HostDataWidth, DeviceDataWidth)
);

  `uvm_component_param_utils(push_pull_agent_cov#(HostDataWidth, DeviceDataWidth))

  // the base class provides the following handles for use:
  // push_pull_agent_cfg: cfg

  // covergroups

  function new(string name, uvm_component parent);
    super.new(name, parent);
    // instantiate all covergroups here
  endfunction : new

endclass
