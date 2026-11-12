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
  nvm_otp_key_agent m_key_agent;

  // A backdoor utility for the data array
  rram_ctrl_bkdr_util m_data_bkdr_util;

  // A backdoor utility for the info array
  rram_ctrl_bkdr_util m_info_bkdr_util;

  // Standard SV/UVM methods
  extern function new(string name="", uvm_component parent=null);
  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);
endclass : rram_ctrl_env


function rram_ctrl_env::new(string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction : new

function void rram_ctrl_env::build_phase(uvm_phase phase);
  string data_bkdr_path, info_bkdr_path;
  int unsigned data_depth, data_nbits, info_depth, info_nbits;

  super.build_phase(phase);

  // Retrieve virtual interfaces
  if (!uvm_config_db#(virtual clk_rst_if)::get(this, "", "otp_clk_rst_vif",
      cfg.otp_clk_rst_vif)) begin
    `uvm_fatal("no_vif", "Failed to get otp_clk_rst_vif from uvm_config_db")
  end
  if (!uvm_config_db#(virtual nvm_otp_key_if)::get(this, "", "otp_key_vif",
                                                   cfg.m_key_agent_cfg.m_vif)) begin
    `uvm_fatal("no_vif", "Failed to get otp_key_vif from uvm_config_db.")
  end

  // Retrieve the DUT's configured FIFO depths
  if (!uvm_config_db#(int unsigned)::get(this, "", "WrFifoDepth", cfg.m_wr_fifo_depth)) begin
    `uvm_fatal("db_cfg", "Failed to get WrFifoDepth from uvm_config_db")
  end
  if (!uvm_config_db#(int unsigned)::get(this, "", "RdFifoDepth", cfg.m_rd_fifo_depth)) begin
    `uvm_fatal("db_cfg", "Failed to get RdFifoDepth from uvm_config_db")
  end
  if (!uvm_config_db#(string)::get(this, "", "data_bkdr_path", data_bkdr_path)) begin
    `uvm_fatal("db_cfg", "Failed to get data_bkdr_path from uvm_config_db.")
  end
  if (!uvm_config_db#(int unsigned)::get(this, "", "data_bkdr_depth", data_depth)) begin
    `uvm_fatal("db_cfg", "Failed to get data_bkdr_depth from uvm_config_db.")
  end
  if (!uvm_config_db#(int unsigned)::get(this, "", "data_bkdr_nbits", data_nbits)) begin
    `uvm_fatal("db_cfg", "Failed to get data_bkdr_nbits from uvm_config_db.")
  end
  if (!uvm_config_db#(string)::get(this, "", "info_bkdr_path", info_bkdr_path)) begin
    `uvm_fatal("db_cfg", "Failed to get info_bkdr_path from uvm_config_db.")
  end
  if (!uvm_config_db#(int unsigned)::get(this, "", "info_bkdr_depth", info_depth)) begin
    `uvm_fatal("db_cfg", "Failed to get info_bkdr_depth from uvm_config_db.")
  end
  if (!uvm_config_db#(int unsigned)::get(this, "", "info_bkdr_nbits", info_nbits)) begin
    `uvm_fatal("db_cfg", "Failed to get info_bkdr_nbits from uvm_config_db.")
  end

  m_key_agent = nvm_otp_key_agent::type_id::create("m_key_agent", this);
  uvm_config_db#(nvm_otp_key_agent_cfg)::set(this, "m_key_agent", "cfg", cfg.m_key_agent_cfg);

  m_data_bkdr_util = new("m_data_bkdr_util", data_bkdr_path, data_depth, data_nbits,
                         mem_bkdr_util_pkg::ErrDetectionNone);
  m_info_bkdr_util = new("m_info_bkdr_util", info_bkdr_path, info_depth, info_nbits,
                         mem_bkdr_util_pkg::ErrDetectionNone);
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
