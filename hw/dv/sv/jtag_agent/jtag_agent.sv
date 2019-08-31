// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class jtag_agent extends dv_base_agent #(
      .CFG_T          (jtag_agent_cfg),
      .DRIVER_T       (jtag_driver),
      .SEQUENCER_T    (jtag_sequencer),
      .MONITOR_T      (jtag_monitor),
      .COV_T          (jtag_agent_cov)
  );

  `uvm_component_utils(jtag_agent)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // get jtag_if handle
    if (!uvm_config_db#(virtual jtag_if)::get(this, "", "vif", cfg.vif))
      `uvm_fatal(`gfn, "failed to get jtag_if handle from uvm_config_db")
  endfunction

endclass
