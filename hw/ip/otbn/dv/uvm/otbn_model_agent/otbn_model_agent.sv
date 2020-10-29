// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otbn_model_agent extends dv_base_agent #(
  .CFG_T          (otbn_model_agent_cfg),
  .MONITOR_T      (otbn_model_monitor)
);

  `uvm_component_utils(otbn_model_agent)
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // This agent doesn't support active use (it's just for monitoring the model interface).
    `DV_CHECK_FATAL(!cfg.is_active)

    // get otbn_model_if handle
    if (!uvm_config_db#(virtual otbn_model_if)::get(this, "", "vif", cfg.vif)) begin
      `uvm_fatal(`gfn, "failed to get otbn_model_if handle from uvm_config_db")
    end
  endfunction

endclass
