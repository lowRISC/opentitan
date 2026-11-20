// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Plays otp_ctrl on the NVM scrambling-key interface (nvm_otp_key_if): the DUT requests the
// address and data scrambling keys and this agent answers.
//
// The work is split the usual way:
// - nvm_otp_key_monitor sees each request and passes it to the sequencer, and publishes each
//   completed handshake on monitor.analysis_port for the environment's scoreboard.
// - nvm_otp_key_device_seq picks the response.
// - nvm_otp_key_device_driver drives it.
//
// The virtual interface is fetched from uvm_config_db under the name "vif".
class nvm_otp_key_agent extends dv_reactive_agent #(
  .CFG_T       (nvm_otp_key_agent_cfg),
  .DRIVER_T    (nvm_otp_key_device_driver),
  .SEQUENCER_T (nvm_otp_key_sequencer),
  .MONITOR_T   (nvm_otp_key_monitor),
  .COV_T       (nvm_otp_key_agent_cov)
);
  `uvm_component_utils(nvm_otp_key_agent)

  extern function new(string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);
endclass : nvm_otp_key_agent

function nvm_otp_key_agent::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction : new

function void nvm_otp_key_agent::build_phase(uvm_phase phase);
  super.build_phase(phase);

  if (cfg.if_mode != Device) begin
    `uvm_fatal(`gfn, "nvm_otp_key_agent only supports Device mode (the DUT is the requester)")
  end
  if (!cfg.has_req_fifo) begin
    `uvm_fatal(`gfn, "nvm_otp_key_agent needs cfg.has_req_fifo to pass requests to the sequence")
  end

  if (!uvm_config_db#(virtual nvm_otp_key_if)::get(this, "", "vif", cfg.vif)) begin
    `uvm_fatal(`gfn, "Failed to get nvm_otp_key_if handle from uvm_config_db")
  end
endfunction : build_phase

task nvm_otp_key_agent::run_phase(uvm_phase phase);
  nvm_otp_key_device_seq seq;

  super.run_phase(phase);
  if (!cfg.is_active || !cfg.start_default_seq) return;

  seq = nvm_otp_key_device_seq::type_id::create("seq");
  `DV_CHECK_RANDOMIZE_FATAL(seq)
  seq.start(sequencer);
endtask : run_phase
