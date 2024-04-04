// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aes_env extends cip_base_env #(
    .CFG_T              (aes_env_cfg),
    .COV_T              (aes_env_cov),
    .VIRTUAL_SEQUENCER_T(aes_virtual_sequencer),
    .SCOREBOARD_T       (aes_scoreboard)
  );
  `uvm_component_utils(aes_env)

  `uvm_component_new

  key_sideload_agent keymgr_sideload_agent;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    keymgr_sideload_agent = key_sideload_agent#(keymgr_pkg::hw_key_req_t)::type_id::create(
      "keymgr_sideload_agent", this);
    uvm_config_db#(key_sideload_agent_cfg#(keymgr_pkg::hw_key_req_t))::set(
      this, "keymgr_sideload_agent*", "cfg", cfg.keymgr_sideload_agent_cfg);
    if (!uvm_config_db#(virtual pins_if #($bits(lc_ctrl_pkg::lc_tx_t) +1 ))::
         get(this, "", "lc_escalate_vif", cfg.lc_escalate_vif)) begin
      `uvm_fatal(`gfn, "failed to get lc_escalate_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual pins_if #(1))::
         get(this, "", "idle_vif", cfg.idle_vif)) begin
      `uvm_fatal(`gfn, "failed to get idle_vif from uvm_config_db")
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    virtual_sequencer.key_sideload_sequencer_h = keymgr_sideload_agent.sequencer;

    // Configure the key sideload sequencer to use UVM_SEQ_ARB_STRICT_FIFO arbitration. This makes
    // sure that we can inject our own sequence if we need to override the default for a bit.
    keymgr_sideload_agent.sequencer.set_arbitration(UVM_SEQ_ARB_STRICT_FIFO);
    // connect keymanager monitor to scoreboard
    if (cfg.en_scb) begin
      keymgr_sideload_agent.monitor.analysis_port.connect(
                        scoreboard.key_manager_fifo.analysis_export);
    end
  endfunction

endclass
