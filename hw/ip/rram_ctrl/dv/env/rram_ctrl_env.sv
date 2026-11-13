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

  // Answer the DUT's OTP scrambling-key requests. See rram_ctrl_otp_key_driver.sv.
  rram_ctrl_otp_key_driver m_otp_addr_key_driver;
  rram_ctrl_otp_key_driver m_otp_data_key_driver;

  // Acts as otp_ctrl on the OTP macro interface
  local otp_macro_agent m_otp_macro_agent;

  // Standard SV/UVM methods
  extern function new(string name="", uvm_component parent=null);
  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);

  // Returns the sequencer that sends commands on the OTP macro interface.
  extern function otp_macro_sequencer get_otp_macro_sequencer();
endclass : rram_ctrl_env


function rram_ctrl_env::new(string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction : new

function void rram_ctrl_env::build_phase(uvm_phase phase);
  super.build_phase(phase);

  // Retrieve the otp_clk_rst_if virtual interface
  if (!uvm_config_db#(virtual clk_rst_if)::get(this, "", "otp_clk_rst_vif",
      cfg.otp_clk_rst_vif)) begin
    `uvm_fatal(`gfn, "failed to get otp_clk_rst_vif from uvm_config_db")
  end

  // Retrieve the DUT's configured FIFO depths
  if (!uvm_config_db#(int unsigned)::get(this, "", "WrFifoDepth", cfg.m_wr_fifo_depth)) begin
    `uvm_fatal(`gfn, "Failed to get WrFifoDepth from uvm_config_db")
  end
  if (!uvm_config_db#(int unsigned)::get(this, "", "RdFifoDepth", cfg.m_rd_fifo_depth)) begin
    `uvm_fatal(`gfn, "Failed to get RdFifoDepth from uvm_config_db")
  end

  m_otp_addr_key_driver = rram_ctrl_otp_key_driver::type_id::create("m_otp_addr_key_driver", this);
  m_otp_addr_key_driver.phase_kind = RramCtrlOtpKeyAddr;

  m_otp_data_key_driver = rram_ctrl_otp_key_driver::type_id::create("m_otp_data_key_driver", this);
  m_otp_data_key_driver.phase_kind = RramCtrlOtpKeyData;

  if (!uvm_config_db#(rram_ctrl_otp_bkdr_util)::get(this, "", "otp_bkdr", cfg.m_otp_bkdr)) begin
    `uvm_fatal(`gfn, "Failed to get otp_bkdr from uvm_config_db")
  end

  if (!uvm_config_db#(virtual otp_macro_if)::get(this, "", "otp_macro_vif",
                                                 cfg.m_otp_macro_agent_cfg.m_vif)) begin
    `uvm_fatal(`gfn, "Failed to get otp_macro_vif from uvm_config_db")
  end
  cfg.m_otp_macro_agent_cfg.en_cov = cfg.en_cov;
  uvm_config_db#(otp_macro_agent_cfg)::set(this, "m_otp_macro_agent", "cfg",
                                           cfg.m_otp_macro_agent_cfg);
  m_otp_macro_agent = otp_macro_agent::type_id::create("m_otp_macro_agent", this);
endfunction : build_phase

function void rram_ctrl_env::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  // See rram_ctrl_scoreboard.sv: the predictor itself lives there, since only the scoreboard has
  // direct cfg/ral access, but only the env has access to the TL agents to connect it up.
  if (cfg.en_scb) begin
    m_tl_agents[cfg.ral.get_name()].monitor.d_chan_port.connect(
        scoreboard.m_tl_core_reg_predictor_filter.analysis_export);
    m_otp_macro_agent.analysis_port.connect(scoreboard.m_otp_macro_imp);
  end
endfunction : connect_phase

function otp_macro_sequencer rram_ctrl_env::get_otp_macro_sequencer();
  return m_otp_macro_agent.sequencer;
endfunction : get_otp_macro_sequencer
