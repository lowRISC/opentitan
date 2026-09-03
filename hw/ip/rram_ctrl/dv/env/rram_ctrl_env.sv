// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_ctrl_env extends cip_base_env #(
    .CFG_T              (rram_ctrl_env_cfg),
    .COV_T              (rram_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T(rram_ctrl_virtual_sequencer),
    .SCOREBOARD_T       (rram_ctrl_scoreboard)
  );
  `uvm_component_utils(rram_ctrl_env)

  // Standard SV/UVM methods
  extern function new(string name="", uvm_component parent=null);
  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);
endclass : rram_ctrl_env


function rram_ctrl_env::new(string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction : new

function void rram_ctrl_env::build_phase(uvm_phase phase);
  super.build_phase(phase);

  // Retrieve the rram_ctrl_otp_key_if virtual interface
  if (!uvm_config_db#(otp_key_vif_t)::get(this, "", "otp_key_vif", cfg.otp_key_vif)) begin
    `uvm_fatal(`gfn, "Failed to get otp_key_vif from uvm_config_db")
  end

  // Retrieve the otp_clk_rst_if virtual interface
  if (!uvm_config_db#(virtual clk_rst_if)::get(this, "", "otp_clk_rst_vif",
      cfg.otp_clk_rst_vif)) begin
    `uvm_fatal(`gfn, "failed to get otp_clk_rst_vif from uvm_config_db")
  end
endfunction : build_phase

function void rram_ctrl_env::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
endfunction : connect_phase
