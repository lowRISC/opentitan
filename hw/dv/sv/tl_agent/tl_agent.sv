// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// TileLink agent
// ---------------------------------------------
class tl_agent extends dv_base_agent#(
    .CFG_T           (tl_agent_cfg),
    .DRIVER_T        (tl_base_driver),
    .HOST_DRIVER_T   (tl_host_driver),
    .DEVICE_DRIVER_T (tl_device_driver),
    .SEQUENCER_T     (tl_sequencer),
    .MONITOR_T       (tl_monitor),
    .COV_T           (tl_agent_cov)
  );

  `uvm_component_utils(tl_agent)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // get tl_if handle
    if (!uvm_config_db#(virtual tl_if)::get(this, "", "vif", cfg.vif)) begin
      `uvm_fatal(`gfn, "failed to get tl_if handle from uvm_config_db")
    end
    cfg.vif.if_mode = cfg.if_mode;
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.if_mode == dv_utils_pkg::Device) begin
      if (cfg.device_can_rsp_on_same_cycle) begin
        monitor.a_chan_same_cycle_rsp_port.connect(sequencer.a_chan_req_fifo.analysis_export);
      end else begin
        monitor.a_chan_port.connect(sequencer.a_chan_req_fifo.analysis_export);
      end
    end
  endfunction
endclass : tl_agent
