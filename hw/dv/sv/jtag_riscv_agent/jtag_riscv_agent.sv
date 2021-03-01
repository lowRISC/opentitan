// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class jtag_riscv_agent extends dv_base_agent #(
      .CFG_T          (jtag_riscv_agent_cfg),
      .SEQUENCER_T    (jtag_riscv_sequencer),
      .MONITOR_T      (jtag_riscv_monitor),
      .COV_T          (jtag_riscv_agent_cov)
  );

  `uvm_component_utils(jtag_riscv_agent)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // get jtag_riscv_if handle
    if (!uvm_config_db#(virtual jtag_riscv_if)::get(this, "", "vif", cfg.vif))
      `uvm_fatal(`gfn, "failed to get jtag_riscv_if handle from uvm_config_db")

    cfg.has_driver = 0;
  endfunction

endclass
