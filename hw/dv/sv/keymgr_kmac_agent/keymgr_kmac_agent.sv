// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class keymgr_kmac_agent extends dv_base_agent #(
  .CFG_T          (keymgr_kmac_agent_cfg),
  .DRIVER_T       (keymgr_kmac_driver),
  .HOST_DRIVER_T  (keymgr_kmac_host_driver),
  .DEVICE_DRIVER_T(keymgr_kmac_device_driver),
  .SEQUENCER_T    (keymgr_kmac_sequencer),
  .MONITOR_T      (keymgr_kmac_monitor),
  .COV_T          (keymgr_kmac_agent_cov)
);

  `uvm_component_utils(keymgr_kmac_agent)

  `uvm_component_new
  push_pull_agent#(`CONNECT_DATA_WIDTH) m_data_push_agent;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // get keymgr_kmac_intf handle
    if (!uvm_config_db#(virtual keymgr_kmac_intf)::get(this, "", "vif", cfg.vif)) begin
      `uvm_fatal(`gfn, "failed to get keymgr_kmac_intf handle from uvm_config_db")
    end

    // create push_agent, agent_cfg
    m_data_push_agent = push_pull_agent#(`CONNECT_DATA_WIDTH)::type_id::create(
        "m_data_push_agent", this);
    cfg.m_data_push_agent_cfg = push_pull_agent_cfg#(`CONNECT_DATA_WIDTH)::type_id::create(
        "m_data_push_agent_cfg");
    cfg.m_data_push_agent_cfg.is_active  = cfg.is_active;
    cfg.m_data_push_agent_cfg.agent_type = PushAgent;
    cfg.m_data_push_agent_cfg.if_mode    = cfg.if_mode;
    cfg.vif.if_mode = cfg.if_mode;

    // pass cfg and vif
    uvm_config_db#(push_pull_agent_cfg#(`CONNECT_DATA_WIDTH))::set(this, "m_data_push_agent*",
                   "cfg", cfg.m_data_push_agent_cfg);
    uvm_config_db#(virtual push_pull_if#(`CONNECT_DATA_WIDTH))::set(this,
                   "m_data_push_agent*", "vif", cfg.vif.req_data_if);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    if (cfg.is_active) begin
      if (cfg.if_mode == dv_utils_pkg::Host) begin
        sequencer.m_push_pull_sequencer = m_data_push_agent.sequencer;
      end else begin
        monitor.req_port.connect(sequencer.req_data_fifo.analysis_export);
      end
    end

    m_data_push_agent.monitor.analysis_port.connect(monitor.data_fifo.analysis_export);
  endfunction

  virtual task run_phase(uvm_phase phase);
    if (cfg.is_active) begin
      keymgr_kmac_device_seq m_seq = keymgr_kmac_device_seq::type_id::create("m_seq", this);
      if (cfg.if_mode == dv_utils_pkg::Device && cfg.start_default_device_seq) begin
        uvm_config_db#(uvm_object_wrapper)::set(null,
                                               {sequencer.get_full_name(), ".run_phase"},
                                               "default_sequence",
                                               m_seq.get_type());
        sequencer.start_phase_sequence(phase);
      end
    end
  endtask
endclass
