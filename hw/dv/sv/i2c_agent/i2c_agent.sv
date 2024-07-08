// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_agent extends dv_base_agent #(
      .CFG_T           (i2c_agent_cfg),
      .DRIVER_T        (i2c_driver),
      .SEQUENCER_T     (i2c_sequencer),
      .MONITOR_T       (i2c_monitor),
      .COV_T           (i2c_agent_cov)
  );

  `uvm_component_utils(i2c_agent)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual i2c_if)::get(this, "", "vif", cfg.vif)) begin
      `uvm_fatal(`gfn, "failed to get i2c_if handle from uvm_config_db")
    end
  endfunction : build_phase

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    // If the monitor is active, connect the in-progress transfer ports from the monitor through
    // to the sequencer. This allows agent sequences to monitor the state of any in-progress
    // i2c transfer, and drive accordingly.
    if (cfg.is_active) begin
      monitor.controller_mode_in_progress_port.connect(
        sequencer.controller_mode_in_progress_fifo.analysis_export);
      monitor.target_mode_in_progress_port.connect(
        sequencer.target_mode_in_progress_fifo.analysis_export);
    end
  endfunction : connect_phase

endclass
