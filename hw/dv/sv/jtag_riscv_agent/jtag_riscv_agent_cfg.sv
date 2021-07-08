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
    // TODO: consider move it to build_phase
    this.has_driver = 0;
  endfunction : new

  // assert trst_n for a number of cycles
  task do_trst_n(int cycles = $urandom_range(5, 20));
    m_jtag_agent_cfg.do_trst_n(cycles);
  endtask

endclass
