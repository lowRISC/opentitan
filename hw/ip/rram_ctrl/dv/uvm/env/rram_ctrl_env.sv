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

  // An agent that acts as otp_ctrl and responds to key requests from rram_ctrl
  otp_key_agent m_key_agent;

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

  // Retrieve virtual interfaces
  if (!uvm_config_db#(virtual clk_rst_if)::get(this, "", "otp_clk_rst_vif",
      cfg.otp_clk_rst_vif)) begin
    `uvm_fatal("no_vif", "Failed to get otp_clk_rst_vif from uvm_config_db")
  end
  if (!uvm_config_db#(virtual otp_key_if)::get(this, "", "otp_key_vif",
                                               cfg.m_key_agent_cfg.m_vif)) begin
    `uvm_fatal("no_vif", "Failed to get otp_key_vif from uvm_config_db.")
  end

  // Retrieve the DUT's configured FIFO depths
  if (!uvm_config_db#(int unsigned)::get(this, "", "WrFifoDepth", cfg.m_wr_fifo_depth)) begin
    `uvm_fatal(`gfn, "Failed to get WrFifoDepth from uvm_config_db")
  end
  if (!uvm_config_db#(int unsigned)::get(this, "", "RdFifoDepth", cfg.m_rd_fifo_depth)) begin
    `uvm_fatal(`gfn, "Failed to get RdFifoDepth from uvm_config_db")
  end

  m_key_agent = otp_key_agent::type_id::create("m_key_agent", this);
  uvm_config_db#(otp_key_agent_cfg)::set(this, "m_key_agent", "cfg", cfg.m_key_agent_cfg);
endfunction : build_phase

function void rram_ctrl_env::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  // See rram_ctrl_scoreboard.sv: the predictor itself lives there, since only the scoreboard has
  // direct cfg/ral access, but only the env has access to the TL agents to connect it up.
  if (cfg.en_scb) begin
    m_tl_agents[cfg.ral.get_name()].monitor.d_chan_port.connect(
        scoreboard.m_tl_core_reg_predictor_filter.analysis_export);
  end

  m_key_agent.monitor.analysis_port.connect(scoreboard.m_otp_key_txn_imp);
endfunction : connect_phase
