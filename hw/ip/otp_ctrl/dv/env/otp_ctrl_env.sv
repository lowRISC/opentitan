// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otp_ctrl_env extends cip_base_env #(
    .CFG_T              (otp_ctrl_env_cfg),
    .COV_T              (otp_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T(otp_ctrl_virtual_sequencer),
    .SCOREBOARD_T       (otp_ctrl_scoreboard)
  );
  `uvm_component_utils(otp_ctrl_env)

  `uvm_component_new

  push_pull_agent#(SRAM_DATA_SIZE) m_sram_pull_agent[NumSramKeyReqSlots];

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // build sram-otp pull interface
    for (int i = 0; i < NumSramKeyReqSlots; i++) begin
      string sram_agent_name = $sformatf("m_sram_pull_agent[%0d]", i);
      m_sram_pull_agent[i] = push_pull_agent#(SRAM_DATA_SIZE)::type_id::create(sram_agent_name,
                                                                               this);
      uvm_config_db#(push_pull_agent_cfg#(SRAM_DATA_SIZE))::set(this,
                     $sformatf("%0s*", sram_agent_name), "cfg", cfg.m_sram_pull_agent_cfg[i]);
    end

    if (!uvm_config_db#(pwr_otp_vif)::get(this, "", "pwr_otp_vif", cfg.pwr_otp_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get pwr_otp_vif from uvm_config_db")
    end
    if (!uvm_config_db#(lc_provision_en_vif)::get(this, "", "lc_provision_en_vif",
                                                  cfg.lc_provision_en_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get lc_provision_en_vif from uvm_config_db")
    end
    if (!uvm_config_db#(mem_bkdr_vif)::get(this, "", "mem_bkdr_vif", cfg.mem_bkdr_vif)) begin
      `uvm_fatal(`gfn, "failed to get mem_bkdr_vif from uvm_config_db")
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    for (int i = 0; i < NumSramKeyReqSlots; i++) begin
      virtual_sequencer.sram_pull_sequencer_h[i] = m_sram_pull_agent[i].sequencer;
      if (cfg.en_scb) begin
        m_sram_pull_agent[i].monitor.req_port.connect(scoreboard.sram_fifo[i].analysis_export);
      end
    end
  endfunction

endclass
