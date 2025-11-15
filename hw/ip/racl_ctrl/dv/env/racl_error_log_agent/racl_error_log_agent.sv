// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class racl_error_log_agent extends dv_base_agent#(.CFG_T      (racl_error_log_agent_cfg),
                                                  .DRIVER_T   (racl_error_log_driver),
                                                  .SEQUENCER_T(racl_error_log_sequencer),
                                                  .MONITOR_T  (racl_error_log_monitor));
  `uvm_component_utils(racl_error_log_agent)

  // An analysis export that exposes error log vector items that have been captured by the monitor
  uvm_analysis_export#(racl_error_log_vec_item) errors_seen;

  extern function new (string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);
endclass

function racl_error_log_agent::new (string name, uvm_component parent);
  super.new(name, parent);
  errors_seen = new("errors_seen", this);
endfunction

function void racl_error_log_agent::build_phase(uvm_phase phase);
  super.build_phase(phase);
  if (cfg.vif == null) `uvm_fatal(`gfn, "Cannot use agent with no log interface.")
endfunction

function void racl_error_log_agent::connect_phase(uvm_phase phase);
  super.connect_phase(phase);

  driver.vif = cfg.vif;
  monitor.vif = cfg.vif;

  monitor.analysis_port.connect(errors_seen);
endfunction

task racl_error_log_agent::run_phase(uvm_phase phase);
  super.run_phase(phase);

  // The agent is in charge of telling the sequencer to stop its sequences if a reset gets asserted.
  // Since there isn't currently a reset agent, we have to spot resets directly.
  forever begin
    wait(cfg.in_reset);
    sequencer.stop_sequences();
    wait(!cfg.in_reset);
  end
endtask
