// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class jtag_riscv_agent_cfg extends dv_base_agent_cfg;
  `uvm_object_utils_begin(jtag_riscv_agent_cfg)
  `uvm_object_utils_end

  jtag_agent_cfg m_jtag_agent_cfg;

  function new (string name="");
    super.new(name);

    // This is a high level agent and will use jtag_agent's driver.
    this.has_driver = 0;
  endfunction : new

endclass
