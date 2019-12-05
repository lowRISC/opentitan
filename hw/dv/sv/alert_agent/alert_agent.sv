// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// Alert agent
// ---------------------------------------------
class alert_agent extends dv_base_agent#(
    .CFG_T           (alert_agent_cfg),
    .DRIVER_T        (alert_base_driver),
    .HOST_DRIVER_T   (alert_sender_driver),
    .DEVICE_DRIVER_T (alert_receiver_driver),
    .SEQUENCER_T     (alert_sequencer),
    .MONITOR_T       (alert_monitor),
    .COV_T           (alert_agent_cov)
  );

  `uvm_component_utils(alert_agent)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // get alert_if handle
    if (!uvm_config_db#(virtual alert_if)::get(this, "", "vif", cfg.vif)) begin
      `uvm_fatal(`gfn, "failed to get alert_if handle from uvm_config_db")
    end
  endfunction

endclass : alert_agent
