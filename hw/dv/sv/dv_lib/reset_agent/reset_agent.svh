// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class reset_agent extends dv_base_agent #(
  .CFG_T          (reset_agent_cfg),
  .DRIVER_T       (reset_driver),
  .SEQUENCER_T    (reset_sequencer),
  .MONITOR_T      (reset_monitor),
  .COV_T          (reset_agent_cov)
);

  `uvm_component_utils(reset_agent)

  uvm_analysis_port #(reset_item) reset_tr_ap;
  uvm_analysis_port #(reset_state_e) reset_st_ap;

  // Standard SV/UVM methods
  extern function new(string name, uvm_component parent = null);
  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);
endclass : reset_agent


function reset_agent::new(string name, uvm_component parent = null);
  super.new(name, parent);
  reset_tr_ap = new("reset_tr_ap", this);
  reset_st_ap = new("reset_st_ap", this);
endfunction : new

function void reset_agent::build_phase(uvm_phase phase);
  super.build_phase(phase);
  if (cfg.vif == null) begin
    `uvm_fatal(`gfn, "failed to get vif from uvm_config_db")
  end
endfunction : build_phase

function void reset_agent::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  // Connect the driver to the sequencer if the agent is ACTIVE
  if (cfg.is_active) begin
    driver.seq_item_port.connect(sequencer.seq_item_export);
  end

  // Connect the analysis ports from the monitor to the agent to simplify further usage
  // while instanciating this agent.
  monitor.reset_item_ap.connect(reset_tr_ap);
  monitor.reset_state_ap.connect(reset_st_ap);

  // Connect the coverage collector port to the monitor
  if (cfg.en_cov) begin
    monitor.reset_item_ap.connect(cov.analysis_imp);
  end
endfunction : connect_phase
