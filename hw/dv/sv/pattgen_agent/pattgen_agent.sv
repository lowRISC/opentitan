// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pattgen_agent extends dv_base_agent #(
  .CFG_T           (pattgen_agent_cfg),
  .DRIVER_T        (pattgen_driver),
  .SEQUENCER_T     (pattgen_sequencer),
  .MONITOR_T       (pattgen_monitor),
  .COV_T           (pattgen_agent_cov)
);
  `uvm_component_utils(pattgen_agent)
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // get pattgen_if handle
    if (!uvm_config_db#(virtual pattgen_if)::get(this, "", "vif", cfg.vif)) begin
      `uvm_fatal(`gfn, "failed to get pattgen_if handle from uvm_config_db")
    end

    `DV_CHECK_NE_FATAL(cfg.if_mode, dv_utils_pkg::Host, "Host mode not supported")
  endfunction

endclass
