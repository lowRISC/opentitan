// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otp_key_agent extends dv_base_agent #(.CFG_T      (otp_key_agent_cfg),
                                            .DRIVER_T   (otp_key_driver),
                                            .SEQUENCER_T(otp_key_sequencer),
                                            .MONITOR_T  (otp_key_monitor));
  `uvm_component_utils(otp_key_agent)

  extern function new (string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);

  // A task that runs the standard otp_key_seq to respond to key requests
  //
  // This sequence never completes
  extern task run_device_seq();
endclass

function otp_key_agent::new (string name, uvm_component parent);
  super.new(name, parent);
endfunction

function void otp_key_agent::build_phase(uvm_phase phase);
  super.build_phase(phase);

  // If cfg.m_vif isn't already supplied, look up a vif interface handle in the config db.
  if (cfg.m_vif == null &&
      !uvm_config_db#(virtual otp_key_if)::get(this, "", "vif", cfg.m_vif)) begin
    `uvm_fatal("no_vif", "Failed to get vif from uvm_config_db")
  end

  // This agent only supports an if_mode of Monitor or Device: it doesn't currently support sending
  // key requests.
  if (cfg.if_mode == dv_utils_pkg::Host) begin
    `uvm_fatal("unsupported_mode", "This agent cannot send key requests.")
  end

  // Set the mode of the interface (since we're now in control of it) to cfg.if_mode, but qualified
  // by is_active.
  //
  // TODO(#32210): This is a bit silly because some of the combinations aren't relevant.
  cfg.m_vif.if_mode = cfg.is_active ? cfg.if_mode : dv_utils_pkg::Monitor;
endfunction

function void otp_key_agent::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  if (cfg.is_active) begin
    driver.m_req_port.connect(sequencer.m_req_fifo.analysis_export);
  end
endfunction

task otp_key_agent::run_device_seq();
  otp_key_seq seq = otp_key_seq::type_id::create("seq");

  if (!cfg.is_active) begin
    `uvm_fatal("passive_seq", "Cannot start device sequence: the agent is passive.")
  end

  if (!seq.randomize()) begin
    `uvm_fatal("failed_rand", "Failed to randomize device sequence")
  end

  seq.start(sequencer);
endtask
