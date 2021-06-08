// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otbn_env extends cip_base_env #(
    .CFG_T              (otbn_env_cfg),
    .COV_T              (otbn_env_cov),
    .VIRTUAL_SEQUENCER_T(otbn_virtual_sequencer),
    .SCOREBOARD_T       (otbn_scoreboard)
  );
  `uvm_component_utils(otbn_env)

  otbn_model_agent   model_agent;
  otbn_trace_monitor trace_monitor;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    cfg.mem_util = OtbnMemUtilMake(cfg.dut_instance_hier);
    `DV_CHECK_FATAL(cfg.mem_util != null);

    model_agent = otbn_model_agent::type_id::create("model_agent", this);
    uvm_config_db#(otbn_model_agent_cfg)::set(this, "model_agent*", "cfg", cfg.model_agent_cfg);
    cfg.model_agent_cfg.en_cov = cfg.en_cov;

    if (!uvm_config_db#(virtual otbn_trace_if)::get(this, "", "trace_vif", cfg.trace_vif)) begin
      `uvm_fatal(`gfn, "failed to get otbn_trace_if handle from uvm_config_db")
    end
    if (!uvm_config_db#(virtual otbn_loop_if)::get(this, "", "loop_vif", cfg.loop_vif)) begin
      `uvm_fatal(`gfn, "failed to get otbn_loop_if handle from uvm_config_db")
    end
    if (!uvm_config_db#(virtual otbn_alu_bignum_if)::get(this, "", "alu_bignum_vif",
                                                         cfg.alu_bignum_vif)) begin
      `uvm_fatal(`gfn, "failed to get otbn_alu_bignum_if handle from uvm_config_db")
    end
    if (!uvm_config_db#(virtual otbn_mac_bignum_if)::get(this, "", "mac_bignum_vif",
                                                         cfg.mac_bignum_vif)) begin
      `uvm_fatal(`gfn, "failed to get otbn_mac_bignum_if handle from uvm_config_db")
    end
    if (!uvm_config_db#(virtual otbn_rf_base_if)::get(this, "", "rf_base_vif",
                                                      cfg.rf_base_vif)) begin
      `uvm_fatal(`gfn, "failed to get otbn_rf_base_if handle from uvm_config_db")
    end

    trace_monitor = otbn_trace_monitor::type_id::create("trace_monitor", this);
    trace_monitor.cfg = cfg;
    trace_monitor.cov = cov;
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    model_agent.monitor.analysis_port.connect(scoreboard.model_fifo.analysis_export);
    trace_monitor.analysis_port.connect(scoreboard.trace_fifo.analysis_export);
  endfunction

  function void final_phase(uvm_phase phase);
    super.final_phase(phase);

    `DV_CHECK_FATAL(cfg.mem_util != null);
    OtbnMemUtilFree(cfg.mem_util);
    cfg.mem_util = null;
  endfunction

endclass
