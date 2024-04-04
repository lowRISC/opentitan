// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class push_pull_agent #(
    parameter int HostDataWidth   = 32,
    parameter int DeviceDataWidth = HostDataWidth
) extends dv_base_agent #(
    .CFG_T      (push_pull_agent_cfg#(HostDataWidth, DeviceDataWidth)),
    .DRIVER_T   (push_pull_driver#(HostDataWidth, DeviceDataWidth)),
    .SEQUENCER_T(push_pull_sequencer#(HostDataWidth, DeviceDataWidth)),
    .MONITOR_T  (push_pull_monitor#(HostDataWidth, DeviceDataWidth)),
    .COV_T      (push_pull_agent_cov#(HostDataWidth, DeviceDataWidth))
);

  `uvm_component_param_utils(push_pull_agent#(HostDataWidth, DeviceDataWidth))

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // use for reactive device
    cfg.has_req_fifo = 1;

    // get push_pull_if handle
    if (!uvm_config_db#(virtual push_pull_if#(HostDataWidth, DeviceDataWidth))::get(
        this, "", "vif", cfg.vif)) begin
      `uvm_fatal(`gfn, "failed to get push_pull_if handle from uvm_config_db")
    end
    cfg.vif.if_mode = cfg.if_mode;
    cfg.vif.is_push_agent = (cfg.agent_type == PushAgent);
    cfg.vif.in_bidirectional_mode = cfg.in_bidirectional_mode;
    cfg.vif.is_pull_handshake_4_phase = (cfg.pull_handshake_type == FourPhase);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.if_mode == dv_utils_pkg::Device) begin
      monitor.req_analysis_port.connect(sequencer.req_analysis_fifo.analysis_export);
    end
  endfunction

  virtual task run_phase(uvm_phase phase);
    push_pull_device_seq#(HostDataWidth, DeviceDataWidth) m_seq =
        push_pull_device_seq#(HostDataWidth, DeviceDataWidth)::type_id::create("m_seq", this);
    if (cfg.if_mode == dv_utils_pkg::Device && cfg.start_default_device_seq) begin
      uvm_config_db#(uvm_object_wrapper)::set(null, {sequencer.get_full_name(), ".run_phase"},
                                              "default_sequence", m_seq.get_type());
      sequencer.start_phase_sequence(phase);
    end
  endtask

endclass
