// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rng_agent extends dv_base_agent #(
  .CFG_T          (rng_agent_cfg),
  .DRIVER_T       (rng_driver),
  .SEQUENCER_T    (rng_sequencer),
  .MONITOR_T      (rng_monitor),
  .COV_T          (rng_agent_cov)
);

  `uvm_component_utils(rng_agent)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // get rng_if handle
    if (!uvm_config_db#(virtual rng_if)::get(this, "", "vif", cfg.vif)) begin
      `uvm_fatal(`gfn, "failed to get rng_if handle from uvm_config_db")
    end
  endfunction

endclass
