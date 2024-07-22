// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_env extends cip_base_env #(
    .CFG_T              (entropy_src_env_cfg),
    .COV_T              (entropy_src_env_cov),
    .VIRTUAL_SEQUENCER_T(entropy_src_virtual_sequencer),
    .SCOREBOARD_T       (entropy_src_scoreboard)
  );
  `uvm_component_utils(entropy_src_env)

  push_pull_agent#(.HostDataWidth(entropy_src_pkg::RNG_BUS_WIDTH))         m_rng_agent;
  push_pull_agent#(.HostDataWidth(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH))  m_csrng_agent;
  push_pull_agent#(.HostDataWidth(0))                                      m_aes_halt_agent;
  entropy_src_xht_agent                                                    m_xht_agent;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Lookup the CSRNG auxiliary reset. (Is only applied at end-of-sim)
    if (!uvm_config_db#(virtual clk_rst_if)::get(this, "", "csrng_rst_vif", cfg.csrng_rst_vif))
      begin
        `uvm_fatal(`gfn, "failed to get csrng_rst_if from uvm_config_db")
      end

    m_rng_agent = push_pull_agent#(.HostDataWidth(entropy_src_pkg::RNG_BUS_WIDTH))::type_id::
                  create("m_rng_agent", this);
    uvm_config_db#(push_pull_agent_cfg#(.HostDataWidth(entropy_src_pkg::RNG_BUS_WIDTH)))::set
                  (this, "m_rng_agent*", "cfg", cfg.m_rng_agent_cfg);
    cfg.m_rng_agent_cfg.agent_type = push_pull_agent_pkg::PushAgent;
    cfg.m_rng_agent_cfg.if_mode    = dv_utils_pkg::Host;
    cfg.m_rng_agent_cfg.en_cov     = cfg.en_cov;

    // To correctly model ast/rng behavior, back-to-back entropy is not allowed
    // The actual AST/RNG ingores ready-signal backpressure, but this can be inconvenient for
    // tests which use a fixed (non-random) RNG sequence.  So the backpressure support is done
    // on a test by test basis.
    cfg.m_rng_agent_cfg.zero_delays = 0;
    cfg.m_rng_agent_cfg.host_delay_min = 1;
    cfg.m_rng_agent_cfg.host_delay_max = cfg.rng_max_delay;
    cfg.m_rng_agent_cfg.ignore_push_host_backpressure = cfg.rng_ignores_backpressure;

    m_csrng_agent = push_pull_agent#(.HostDataWidth(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH))::
                    type_id::create("m_csrng_agent", this);
    uvm_config_db#(push_pull_agent_cfg#(.HostDataWidth(entropy_src_pkg::FIPS_CSRNG_BUS_WIDTH)))::set
                  (this, "m_csrng_agent*", "cfg", cfg.m_csrng_agent_cfg);
    cfg.m_csrng_agent_cfg.agent_type = push_pull_agent_pkg::PullAgent;
    cfg.m_csrng_agent_cfg.if_mode    = dv_utils_pkg::Host;
    cfg.m_csrng_agent_cfg.en_cov     = cfg.en_cov;

    m_aes_halt_agent = push_pull_agent#(.HostDataWidth(0))::
                      type_id::create("m_aes_halt_agent", this);
    uvm_config_db#(push_pull_agent_cfg#(.HostDataWidth(0)))::set
                  (this, "m_aes_halt_agent*", "cfg", cfg.m_aes_halt_agent_cfg);
    cfg.m_aes_halt_agent_cfg.agent_type          = push_pull_agent_pkg::PullAgent;
    cfg.m_aes_halt_agent_cfg.if_mode             = dv_utils_pkg::Device;
    cfg.m_aes_halt_agent_cfg.pull_handshake_type = push_pull_agent_pkg::FourPhase;
    // When CSRNG has just started operating its AES, it may take up to 48 cycles to acknowledge
    // the request. When running ast/rng at the maximum rate (this is an unrealistic scenario
    // primarily used for reaching coverage metrics) we reduce the acknowledge delay to the minimum
    // to reduce backpressure and avoid entropy bits from being dropped from the pipeline as our
    // scoreboard cannot handle this.
    cfg.m_aes_halt_agent_cfg.zero_delays = 0;
    cfg.m_aes_halt_agent_cfg.device_delay_min = 0;
    cfg.m_aes_halt_agent_cfg.device_delay_max = 48;
    // CSRNG drops its ack in the cycle after entropy_src has dropped its req.
    cfg.m_aes_halt_agent_cfg.ack_lo_delay_max = 1;

    m_xht_agent = entropy_src_xht_agent::type_id::create("m_xht_agent", this);
    uvm_config_db#(entropy_src_xht_agent_cfg)::set(this, "m_xht_agent*",
                                                   "cfg", cfg.m_xht_agent_cfg);
    cfg.m_xht_agent_cfg.start_default_seq = 1'b0;
    cfg.m_xht_agent_cfg.if_mode           = dv_utils_pkg::Device;
    cfg.m_xht_agent_cfg.en_cov            = cfg.en_cov;
    cfg.m_xht_agent_cfg.is_active         = 1'b1;

    // When running ast/rng at the maximum rate (this is an unrealistic scenario primarily used for
    // reaching coverage metrics) we reduce the maximum d_ready delay of the TL-UL host to speed up
    // e.g. the reading out of the Observe FIFO.
    if (cfg.rng_max_delay == 1) begin
      cfg.m_tl_agent_cfg.d_ready_delay_max = 5;
    end

    if (!uvm_config_db#(virtual entropy_subsys_fifo_exception_if#(1))::get(this, "",
                        "precon_fifo_vif", cfg.precon_fifo_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get precon_fifo_vif from uvm_config_db")
    end

    if (!uvm_config_db#(virtual entropy_subsys_fifo_exception_if#(1))::get(this, "",
                        "bypass_fifo_vif", cfg.bypass_fifo_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get precon_fifo_vif from uvm_config_db")
    end

    if (!uvm_config_db#(virtual entropy_src_fsm_cov_if)::get(this, "",
                        "main_sm_cov_vif", cfg.fsm_tracking_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get fsm_tracking_vif from uvm_config_db")
    end

    if (!uvm_config_db#(virtual pins_if#(8))::get(this, "", "otp_en_es_fw_read_vif",
        cfg.otp_en_es_fw_read_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get otp_en_es_fw_read_vif from uvm_config_db")
    end
    if (!uvm_config_db#(virtual pins_if#(8))::get(this, "", "otp_en_es_fw_over_vif",
        cfg.otp_en_es_fw_over_vif)) begin
      `uvm_fatal(get_full_name(), "failed to get otp_en_es_fw_over_vif from uvm_config_db")
    end
    // config entropy_src path virtual interface
    if (!uvm_config_db#(virtual entropy_src_path_if)::get(this, "", "entropy_src_path_vif",
         cfg.entropy_src_path_vif)) begin
      `uvm_fatal(`gfn, "failed to get entropy_src_path_vif from uvm_config_db")
    end
    if (!uvm_config_db#(intr_vif)::get(this, "", "intr_vif",
         cfg.interrupt_vif)) begin
      `uvm_fatal(`gfn, "failed to get entropy_src_path_vif from uvm_config_db")
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);

    m_rng_agent.monitor.analysis_port.connect(scoreboard.rng_fifo.analysis_export);
    m_csrng_agent.monitor.analysis_port.connect(scoreboard.csrng_fifo.analysis_export);
    m_xht_agent.monitor.analysis_port.connect(scoreboard.xht_fifo.analysis_export);

    scoreboard.interrupt_vif = cfg.interrupt_vif;

    virtual_sequencer.csrng_sequencer_h    = m_csrng_agent.sequencer;
    virtual_sequencer.rng_sequencer_h      = m_rng_agent.sequencer;
    virtual_sequencer.aes_halt_sequencer_h = m_aes_halt_agent.sequencer;
    virtual_sequencer.xht_sequencer        = m_xht_agent.sequencer;

  endfunction

endclass
