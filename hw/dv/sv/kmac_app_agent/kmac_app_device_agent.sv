// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_app_device_agent extends dv_base_agent #(.CFG_T       (kmac_app_agent_cfg),
                                                    .DRIVER_T    (kmac_app_device_driver),
                                                    .SEQUENCER_T (kmac_app_device_sequencer),
                                                    .MONITOR_T   (kmac_app_monitor),
                                                    .COV_T       (kmac_app_agent_cov));
  `uvm_component_utils(kmac_app_device_agent)

  extern function new(string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);

  // A task that runs the standard kmac_app_device_seq to respond to app requests
  //
  // This sequence never completes
  extern task run_device_seq();
endclass

function kmac_app_device_agent::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction

function void kmac_app_device_agent::build_phase(uvm_phase phase);
  super.build_phase(phase);

  // Get the handle to the interface
  if (!uvm_config_db#(virtual kmac_app_if)::get(this, "", "vif", cfg.vif)) begin
    `uvm_fatal(`gfn, "failed to get kmac_app_if handle from uvm_config_db")
  end

  // Configure the interface to match the agent.
  cfg.vif.if_mode = cfg.is_active ? Device : Monitor;
endfunction

function void kmac_app_device_agent::connect_phase(uvm_phase phase);
  super.connect_phase(phase);

  if (cfg.is_active) begin
    // Connect requests from the driver to the sequencer
    driver.m_req_port.connect(sequencer.m_req_fifo.analysis_export);
  end
endfunction

task kmac_app_device_agent::run_device_seq();
  kmac_app_device_seq seq = kmac_app_device_seq::type_id::create("seq");
  if (!seq.randomize()) `uvm_fatal(get_full_name(), "Failed to randomize device seq")
  seq.start(sequencer);
endtask
