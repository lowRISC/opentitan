// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class csrng_agent extends dv_base_agent #(
  .CFG_T          (csrng_agent_cfg),
  .DRIVER_T       (csrng_driver),
  .HOST_DRIVER_T  (csrng_host_driver),
  .DEVICE_DRIVER_T(csrng_device_driver),
  .SEQUENCER_T    (csrng_sequencer),
  .MONITOR_T      (csrng_monitor),
  .COV_T          (csrng_agent_cov)
);

  `uvm_component_utils(csrng_agent)
  `uvm_component_new

  push_pull_agent#(.HostDataWidth(csrng_pkg::CSRNG_CMD_WIDTH))          m_req_push_agent;
  push_pull_agent#(.HostDataWidth(csrng_pkg::FIPS_GENBITS_BUS_WIDTH))   m_genbits_push_agent;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // get csrng_if handle
    if (!uvm_config_db#(virtual csrng_if)::get(this, "", "vif", cfg.vif)) begin
      `uvm_fatal(`gfn, "failed to get csrng_if handle from uvm_config_db")
    end

    // create agents, agent_cfgs
    m_req_push_agent = push_pull_agent#(csrng_pkg::CSRNG_CMD_WIDTH)::type_id::
                       create("m_req_push_agent", this);
    cfg.m_req_push_agent_cfg = push_pull_agent_cfg#(csrng_pkg::CSRNG_CMD_WIDTH)::type_id::
                               create("m_req_push_agent.cfg");
    cfg.m_req_push_agent_cfg.is_active   = cfg.is_active;
    cfg.m_req_push_agent_cfg.agent_type  = PushAgent;
    cfg.m_req_push_agent_cfg.if_mode     = cfg.if_mode;

    m_genbits_push_agent = push_pull_agent#(csrng_pkg::FIPS_GENBITS_BUS_WIDTH)::type_id::
                           create("m_genbits_push_agent", this);
    cfg.m_genbits_push_agent_cfg = push_pull_agent_cfg#(csrng_pkg::FIPS_GENBITS_BUS_WIDTH)::type_id::
                                   create("m_genbits_push_agent_cfg");
    cfg.m_genbits_push_agent_cfg.is_active  = cfg.is_active;
    cfg.m_genbits_push_agent_cfg.agent_type = PushAgent;
    if (cfg.if_mode == dv_utils_pkg::Host) begin
      cfg.m_genbits_push_agent_cfg.if_mode = dv_utils_pkg::Device;
    end else begin
      cfg.has_req_fifo = 1;
      cfg.m_genbits_push_agent_cfg.if_mode = dv_utils_pkg::Host;
    end

    cfg.vif.if_mode = cfg.if_mode;

    // pass cfg and vif
    uvm_config_db#(push_pull_agent_cfg#(csrng_pkg::CSRNG_CMD_WIDTH))::set(this,
         "m_req_push_agent*", "cfg", cfg.m_req_push_agent_cfg);
    uvm_config_db#(push_pull_agent_cfg#(csrng_pkg::FIPS_GENBITS_BUS_WIDTH))::set(this,
         "m_genbits_push_agent*", "cfg", cfg.m_genbits_push_agent_cfg);

    uvm_config_db#(virtual push_pull_if#(csrng_pkg::CSRNG_CMD_WIDTH))::set(this,
         "m_req_push_agent*", "vif", cfg.vif.req_push_if);
    uvm_config_db#(virtual push_pull_if#(csrng_pkg::FIPS_GENBITS_BUS_WIDTH))::set(this,
         "m_genbits_push_agent*", "vif", cfg.vif.genbits_push_if);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    if (cfg.is_active) begin
      if (cfg.if_mode == dv_utils_pkg::Device) begin
        monitor.req_analysis_port.connect(sequencer.req_analysis_fifo.analysis_export);
        sequencer.m_genbits_push_sequencer = m_genbits_push_agent.sequencer;
      end
    end
  endfunction

endclass
