// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class alert_agent_cov extends dv_base_agent_cov #(alert_agent_cfg);

  `uvm_component_utils(alert_agent_cov)

  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction : new

endclass
