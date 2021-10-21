// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ast_adc_agent extends dv_base_agent #(
  .CFG_T          (ast_adc_agent_cfg),
  .DRIVER_T       (ast_adc_driver),
  .SEQUENCER_T    (ast_adc_sequencer),
  .MONITOR_T      (ast_adc_monitor),
  .COV_T          (ast_adc_agent_cov)
);

  `uvm_component_utils(ast_adc_agent)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // get ast_adc_if handle
    if (!uvm_config_db#(virtual ast_adc_if)::get(this, "", "vif", cfg.vif)) begin
      `uvm_fatal(`gfn, "failed to get ast_adc_if handle from uvm_config_db")
    end
  endfunction

endclass
