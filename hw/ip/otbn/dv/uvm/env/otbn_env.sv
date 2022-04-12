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

  otbn_model_agent    model_agent;
  otbn_trace_monitor  trace_monitor;
  otbn_sideload_agent keymgr_sideload_agent;
  otp_key_agent       key_agent;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    cfg.mem_util = OtbnMemUtilMake(cfg.dut_instance_hier);
    `DV_CHECK_FATAL(cfg.mem_util != null);

    model_agent = otbn_model_agent::type_id::create("model_agent", this);
    uvm_config_db#(otbn_model_agent_cfg)::set(this, "model_agent*", "cfg", cfg.model_agent_cfg);
    cfg.model_agent_cfg.en_cov = cfg.en_cov;

    // Get the OTP clk/rst interface
    if (!uvm_config_db#(virtual clk_rst_if)::get(this, "", "otp_clk_rst_vif",
        cfg.otp_clk_rst_vif)) begin
      `uvm_fatal(`gfn, "failed to get otp_clk_rst_if from uvm_config_db")
    end
    cfg.otp_clk_rst_vif.set_freq_mhz(cfg.otp_freq_mhz);

    keymgr_sideload_agent = otbn_sideload_agent::type_id::create("keymgr_sideload_agent", this);
    uvm_config_db#(otbn_sideload_agent_cfg)::set(
      this, "keymgr_sideload_agent*", "cfg", cfg.keymgr_sideload_agent_cfg);

    key_agent = otp_key_agent::type_id::create("key_agent", this);
    uvm_config_db#(otp_key_agent_cfg)::set(this, "key_agent", "cfg", cfg.key_cfg);
    cfg.key_cfg.agent_type = push_pull_agent_pkg::PullAgent;
    cfg.key_cfg.if_mode = dv_utils_pkg::Device;
    // CDC synchronization between OTP and OTBN clock domains requires that the scrambling seed data
    // should be held for at least a few cycles before it can be safely latched by the OTBN domain.
    // Easy way to do this is just to force the push_pull_agent to hold the data until the next key
    // request is sent out.
    cfg.key_cfg.hold_d_data_until_next_req = 1'b1;
    cfg.key_cfg.zero_delays = 1'b1;
    cfg.key_cfg.en_cov = cfg.en_cov;

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
    if (!uvm_config_db#(virtual otbn_escalate_if)::get(this, "", "escalate_vif",
                                                       cfg.escalate_vif)) begin
      `uvm_fatal(`gfn, "failed to get otbn_escalate_if handle from uvm_config_db")
    end
    if (!uvm_config_db#(mem_bkdr_util)::get(this, "", "imem_util", cfg.imem_util)) begin
      `uvm_fatal(`gfn, "failed to get imem_util from uvm_config_db")
    end
    if (!uvm_config_db#(mem_bkdr_util)::get(this, "", "dmem_util", cfg.dmem_util)) begin
      `uvm_fatal(`gfn, "failed to get dmem_util from uvm_config_db")
    end

    trace_monitor = otbn_trace_monitor::type_id::create("trace_monitor", this);
    trace_monitor.cfg = cfg;
    trace_monitor.cov = cov;
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    model_agent.monitor.analysis_port.connect(scoreboard.model_fifo.analysis_export);
    trace_monitor.analysis_port.connect(scoreboard.trace_fifo.analysis_export);
    cfg.scoreboard = scoreboard;
    virtual_sequencer.key_sideload_sequencer_h = keymgr_sideload_agent.sequencer;

    // Configure the key sideload sequencer to use UVM_SEQ_ARB_STRICT_FIFO arbitration. This makes
    // sure that we can inject our own sequence if we need to override the default for a bit.
    keymgr_sideload_agent.sequencer.set_arbitration(UVM_SEQ_ARB_STRICT_FIFO);
  endfunction

  function void final_phase(uvm_phase phase);
    super.final_phase(phase);

    `DV_CHECK_FATAL(cfg.mem_util != null);
    OtbnMemUtilFree(cfg.mem_util);
    cfg.mem_util = null;
  endfunction

endclass
