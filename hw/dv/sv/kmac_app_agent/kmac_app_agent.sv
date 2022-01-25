// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_app_agent extends dv_base_agent #(
  .CFG_T          (kmac_app_agent_cfg),
  .DRIVER_T       (kmac_app_driver),
  .HOST_DRIVER_T  (kmac_app_host_driver),
  .DEVICE_DRIVER_T(kmac_app_device_driver),
  .SEQUENCER_T    (kmac_app_sequencer),
  .MONITOR_T      (kmac_app_monitor),
  .COV_T          (kmac_app_agent_cov)
);

  `uvm_component_utils(kmac_app_agent)

  `uvm_component_new
  push_pull_agent#(`CONNECT_DATA_WIDTH) m_data_push_agent;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // use for mon-seq connection
    cfg.has_req_fifo = 1;

    // get kmac_app_intf handle
    if (!uvm_config_db#(virtual kmac_app_intf)::get(this, "", "vif", cfg.vif)) begin
      `uvm_fatal(`gfn, "failed to get kmac_app_intf handle from uvm_config_db")
    end

    // create push_agent, agent_cfg
    m_data_push_agent = push_pull_agent#(`CONNECT_DATA_WIDTH)::type_id::create(
        "m_data_push_agent", this);
    cfg.m_data_push_agent_cfg.is_active  = cfg.is_active;
    cfg.m_data_push_agent_cfg.agent_type = PushAgent;
    cfg.m_data_push_agent_cfg.if_mode    = cfg.if_mode;
    cfg.vif.if_mode = cfg.if_mode;
    cfg.m_data_push_agent_cfg.zero_delays = cfg.zero_delays;

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
        monitor.req_analysis_port.connect(sequencer.req_analysis_fifo.analysis_export);
      end
    end

    m_data_push_agent.monitor.analysis_port.connect(monitor.data_fifo.analysis_export);
  endfunction

  virtual task run_phase(uvm_phase phase);
    if (cfg.is_active) begin
      kmac_app_device_seq m_seq = kmac_app_device_seq::type_id::create("m_seq", this);
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
