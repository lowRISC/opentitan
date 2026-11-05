// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Plays otp_ctrl on the OTP macro interface (otp_macro_if): sends Init, Read, Write, ReadRaw,
// WriteRaw and Zeroize requests to the block that stores the OTP contents.
//
// - Sequences (e.g. otp_macro_base_seq) pick each request.
// - otp_macro_host_driver drives it and copies the response back into the item.
// - otp_macro_monitor publishes each completed transaction on monitor.analysis_port for the
//   environment's scoreboard.
//
// The virtual interface is fetched from uvm_config_db under the name "vif".
class otp_macro_agent extends dv_base_agent #(
  .CFG_T       (otp_macro_agent_cfg),
  .DRIVER_T    (otp_macro_host_driver),
  .SEQUENCER_T (otp_macro_sequencer),
  .MONITOR_T   (otp_macro_monitor)
);
  `uvm_component_utils(otp_macro_agent)

  extern function new(string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);
endclass : otp_macro_agent

function otp_macro_agent::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction : new

function void otp_macro_agent::build_phase(uvm_phase phase);
  super.build_phase(phase);

  if (cfg.if_mode != Host) begin
    `uvm_fatal(`gfn, "otp_macro_agent only supports Host mode (the agent plays otp_ctrl)")
  end

  if (!uvm_config_db#(virtual otp_macro_if)::get(this, "", "vif", cfg.vif)) begin
    `uvm_fatal(`gfn, "Failed to get otp_macro_if handle from uvm_config_db")
  end
endfunction : build_phase
