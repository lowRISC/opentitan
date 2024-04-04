// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// ---------------------------------------------
// Alert agent
// ---------------------------------------------
class alert_esc_agent extends dv_base_agent#(
    .CFG_T           (alert_esc_agent_cfg),
    .DRIVER_T        (alert_esc_base_driver),
    .SEQUENCER_T     (alert_esc_sequencer),
    .MONITOR_T       (alert_esc_base_monitor),
    .COV_T           (alert_esc_agent_cov)
  );

  `uvm_component_utils(alert_esc_agent)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    alert_esc_agent_cfg cfg;
    if (!uvm_config_db#(CFG_T)::get(this, "", "cfg", cfg)) begin
      `uvm_fatal(`gfn, $sformatf("failed to get %s from uvm_config_db", cfg.get_type_name()))
    end
    // override monitor
    if (cfg.is_alert) begin
      alert_esc_base_monitor::type_id::set_type_override(alert_monitor::get_type());
    end else begin
      alert_esc_base_monitor::type_id::set_type_override(esc_monitor::get_type());
    end

    // override driver
    if (cfg.is_active) begin
      if (cfg.is_alert) begin
        // use for reactive device
        cfg.has_req_fifo = 1;
        if (cfg.if_mode == Host) begin
          alert_esc_base_driver::type_id::set_type_override(alert_sender_driver::get_type());
        end else begin
          alert_esc_base_driver::type_id::set_type_override(alert_receiver_driver::get_type());
        end
      end else begin
        if (cfg.if_mode == Host) begin
          alert_esc_base_driver::type_id::set_type_override(esc_sender_driver::get_type());
        end else begin
          alert_esc_base_driver::type_id::set_type_override(esc_receiver_driver::get_type());
        end
      end
    end

    super.build_phase(phase);

    void'($value$plusargs("bypass_alert_ready_to_end_check=%0b",
          cfg.bypass_alert_ready_to_end_check));

    // get alert_esc_if handle
    if (!uvm_config_db#(virtual alert_esc_if)::get(this, "", "vif", cfg.vif)) begin
      `uvm_fatal(`gfn, "failed to get alert_esc_if handle from uvm_config_db")
    end
    // get esc_en signal for esc_monitor
    if (cfg.is_active && !cfg.is_alert && cfg.if_mode == Device) begin
      if (!uvm_config_db#(virtual alert_esc_probe_if)::get(this, "", "probe_vif", cfg.probe_vif))
          begin
        `uvm_fatal(`gfn, "failed to get probe_vif handle from uvm_config_db")
      end
    end

    // set variables to alert_esc interface
    cfg.vif.is_async = cfg.is_async;
    cfg.vif.is_alert = cfg.is_alert;
    cfg.vif.is_active = cfg.is_active;
    cfg.vif.if_mode  = cfg.if_mode;
    // set async alert clock frequency
    if (cfg.is_alert && cfg.is_async) begin
      cfg.vif.clk_rst_async_if.set_active(.drive_rst_n_val(0));
      if (cfg.clk_freq_mhz > 0) begin
        int min_freq_mhz = (cfg.clk_freq_mhz / 10) ? (cfg.clk_freq_mhz / 10) : 1;
        cfg.vif.clk_rst_async_if.set_freq_mhz($urandom_range(min_freq_mhz, cfg.clk_freq_mhz * 10));
      end else begin
        cfg.vif.clk_rst_async_if.set_freq_mhz($urandom_range(10, 240));
      end
    end
  endfunction

  // Create automatic response (from monitor) to ping and alert requests.
  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (cfg.is_alert && cfg.has_req_fifo) begin
      monitor.req_analysis_port.connect(sequencer.req_analysis_fifo.analysis_export);
    end
  endfunction

  virtual task run_phase(uvm_phase phase);
    if (cfg.is_alert && cfg.is_active && cfg.start_default_rsp_seq) begin
      // For host mode, run alert ping auto-response sequence.
      if (cfg.if_mode == dv_utils_pkg::Host) begin
        alert_sender_ping_rsp_seq m_seq =
            alert_sender_ping_rsp_seq::type_id::create("m_seq", this);
        uvm_config_db#(uvm_object_wrapper)::set(null, {sequencer.get_full_name(), ".run_phase"},
                                                "default_sequence", m_seq.get_type());
        sequencer.start_phase_sequence(phase);
      end else begin
        // For device mode, run alert auto-response sequence
        alert_receiver_alert_rsp_seq m_seq =
            alert_receiver_alert_rsp_seq::type_id::create("m_seq", this);
        uvm_config_db#(uvm_object_wrapper)::set(null, {sequencer.get_full_name(), ".run_phase"},
                                                "default_sequence", m_seq.get_type());
        sequencer.start_phase_sequence(phase);
      end
    end
  endtask
endclass : alert_esc_agent
