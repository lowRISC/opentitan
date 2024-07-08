// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_sequencer extends dv_base_sequencer#(i2c_item, i2c_agent_cfg);
  `uvm_component_utils(i2c_sequencer)
  `uvm_component_new

  // These ports capture in-progress transfer items published by the i2c_monitor.
  // Agent sequences can then monitor these transfers by accessing the fifos via 'p_sequencer'.
  // Note. that as these items represent in-progress transfers, they are valid and expected to
  // be continuously updated by the monitor until the state variable reaches "StStopped | StAborted"
  // Consumers of these items should not modify them.
  uvm_tlm_analysis_fifo #(i2c_item) controller_mode_in_progress_fifo;
  uvm_tlm_analysis_fifo #(i2c_item) target_mode_in_progress_fifo;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    controller_mode_in_progress_fifo = new("controller_mode_in_progress_fifo", this);
    target_mode_in_progress_fifo = new("target_mode_in_progress_fifo", this);
  endfunction : build_phase

endclass : i2c_sequencer
