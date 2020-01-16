// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ${name}_agent extends dv_base_agent #(
  .CFG_T          (${name}_agent_cfg),
  .DRIVER_T       (${name}_driver),
% if has_separate_host_device_driver:
  .HOST_DRIVER_T  (${name}_host_driver),
  .DEVICE_DRIVER_T(${name}_device_driver),
% endif
  .SEQUENCER_T    (${name}_sequencer),
  .MONITOR_T      (${name}_monitor),
  .COV_T          (${name}_agent_cov)
);

  `uvm_component_utils(${name}_agent)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // get ${name}_if handle
    if (!uvm_config_db#(virtual ${name}_if)::get(this, "", "vif", cfg.vif)) begin
      `uvm_fatal(`gfn, "failed to get ${name}_if handle from uvm_config_db")
    end
  endfunction

endclass
