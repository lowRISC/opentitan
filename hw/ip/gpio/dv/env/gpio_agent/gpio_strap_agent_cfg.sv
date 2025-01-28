// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class gpio_strap_agent_cfg extends dv_base_agent_cfg;
  `uvm_object_utils(gpio_strap_agent_cfg)

  function new (string name = "gpio_strap_agent_cfg");
    super.new(name);
  endfunction : new

endclass
