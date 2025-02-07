// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
`ifndef GPIO_STRAP_AGENT_CFG_SV
`define GPIO_STRAP_AGENT_CFG_SV
class gpio_strap_agent_cfg extends dv_base_agent_cfg;
    `uvm_object_utils(gpio_strap_agent_cfg)
    // Configuration for the gpio_strap_agent
  
    function new (string name = "gpio_strap_agent_cfg");
      super.new(name);
    endfunction : new
  
endclass
`endif // GPIO_STRAP_AGENT_SV