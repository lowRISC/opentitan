// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dv_base_test #(type CFG_T = dv_base_env_cfg,
                     type ENV_T = dv_base_env) extends uvm_test;
  `uvm_component_param_utils(dv_base_test #(CFG_T, ENV_T))

  ENV_T             env;
  CFG_T             cfg;
  bit               run_test_seq = 1'b1;
  string            test_seq_s;

  reset_agent_cfg   rst_agt_cfg;

  uint   max_quit_count  = 1;
  uint64 test_timeout_ns = 200_000_000; // 200ms
  uint   drain_time_ns   = 2_000;  // 2us
  bit    poll_for_stop   = 1'b0;
  uint   poll_for_stop_interval_ns = 1000;
  bit    print_topology  = 1'b0;

  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    dv_report_server  m_dv_report_server = new();
    dv_report_catcher m_report_catcher;
    uvm_report_server::set_server(m_dv_report_server);

    // Message catcher/demoter
    `uvm_create_obj(dv_report_catcher, m_report_catcher)
    // Add demoted messages - we need to do this here to catch build warnings
    add_message_demotes(m_report_catcher);
    // Register catcher
    uvm_report_cb::add(null, m_report_catcher);

    super.build_phase(phase);

    cfg = CFG_T::type_id::create("cfg", this);
    void'($value$plusargs("use_jtag_dmi=%0b", cfg.use_jtag_dmi));
    cfg.initialize();
    `DV_CHECK_RANDOMIZE_FATAL(cfg)

    rst_agt_cfg = reset_agent_cfg::type_id::create("rst_agt_cfg", this);
    config_reset_agent(rst_agt_cfg);

    // Retrieve reset agent interface
    if (!uvm_config_db#(virtual reset_interface)::get(this, "", "reset_vif", rst_agt_cfg.vif)) begin
      `uvm_fatal(`gfn, "failed to get reset_interface from uvm_config_db")
    end

    cfg.rst_agt_cfg = rst_agt_cfg;

    // Enable scoreboard (and sub-scoreboard checks) via plusarg.
    void'($value$plusargs("en_scb=%0b", cfg.en_scb));
    void'($value$plusargs("en_scb_tl_err_chk=%0b", cfg.en_scb_tl_err_chk));
    void'($value$plusargs("en_scb_mem_chk=%0b", cfg.en_scb_mem_chk));
    // Enable fastest design performance by configuring zero delays in all agents.
    void'($value$plusargs("zero_delays=%0b", cfg.zero_delays));

    // Enable coverage collection.
    void'($value$plusargs("en_cov=%0b", cfg.en_cov));

    // Enable reduced runtime test.
    void'($value$plusargs("smoke_test=%0b", cfg.smoke_test));

    // Enable print_topology
    void'($value$plusargs("print_topology=%0b", print_topology));
    uvm_top.enable_print_topology = print_topology;

    void'($value$plusargs("cdc_instrumentation_enabled=%d", cfg.en_dv_cdc));

    uvm_config_db#(CFG_T)::set(this, "*", "cfg", cfg);
    env = ENV_T::type_id::create("env", this);
  endfunction : build_phase

  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    void'($value$plusargs("max_quit_count=%0d", max_quit_count));
    set_max_quit_count(max_quit_count);
    void'($value$plusargs("test_timeout_ns=%0d", test_timeout_ns));
    uvm_top.set_timeout((test_timeout_ns * 1ns));
  endfunction : end_of_elaboration_phase

  virtual task run_phase(uvm_phase phase);
    reset_seq rst_seq;

    void'($value$plusargs("drain_time_ns=%0d", drain_time_ns));
    phase.phase_done.set_drain_time(this, (drain_time_ns * 1ns));
    void'($value$plusargs("poll_for_stop=%0b", poll_for_stop));
    void'($value$plusargs("poll_for_stop_interval_ns=%0d", poll_for_stop_interval_ns));
    if (poll_for_stop) dv_utils_pkg::poll_for_stop(.interval_ns(poll_for_stop_interval_ns));
    void'($value$plusargs("UVM_TEST_SEQ=%0s", test_seq_s));

    // TODO MVy: to be removed, only to test reset on the fly roughly somewhere during the main sequence
    rst_seq = reset_seq::type_id::create("rst_seq");
    fork
      begin
        #100us;
        if (!rst_seq.randomize()) begin
          `uvm_fatal(`gfn, "Failed to randomize transaction !")
        end
        rst_seq.start(env.rst_agt.sequencer);
      end
    join_none

    if (run_test_seq) begin
      run_seq(test_seq_s, phase);
    end
  endtask : run_phase

  // Add message demotes here - hook to use by extended tests
  virtual function void add_message_demotes(dv_report_catcher catcher);
  endfunction

  // Default configuration, can be overwritten if needed
  virtual function void config_reset_agent(reset_agent_cfg rst_agt_cfg);
    // Config items from dv_base_agent_cfg
    rst_agt_cfg.is_active   = 1;
    rst_agt_cfg.has_driver  = 1;
    rst_agt_cfg.en_monitor  = 1;
    rst_agt_cfg.if_mode     = Device;
    rst_agt_cfg.has_reset   = 0;      // It doesn't require this as it is managing it itself

    // Config items from reset_agent_cfg
    rst_agt_cfg.enable_debug_messages = 1;  // TODO MVy: tmp
    rst_agt_cfg.polarity              = ActiveLow;
    rst_agt_cfg.assert_is_sync        = 0;
    rst_agt_cfg.deassert_is_sync      = 1;
    rst_agt_cfg.ini_assert_delay      = 50;
    rst_agt_cfg.ini_assert_width      = 100;
  endfunction : config_reset_agent

  virtual task run_seq(string test_seq_s, uvm_phase phase);
    uvm_sequence test_seq = create_seq_by_name(test_seq_s);

    // Setting the sequencer before the sequence is randomized is mandatory. We do this so that the
    // sequence has access to the UVM environment's cfg handle via the p_sequencer handle within the
    // randomization constraints.
    test_seq.set_sequencer(env.virtual_sequencer);
    `DV_CHECK_RANDOMIZE_FATAL(test_seq)

    `uvm_info(`gfn, {"Starting test sequence ", test_seq_s}, UVM_MEDIUM)
    phase.raise_objection(this, $sformatf("%s objection raised", `gn));
    test_seq.start(env.virtual_sequencer);
    phase.drop_objection(this, $sformatf("%s objection dropped", `gn));
    `uvm_info(`gfn, {"Finished test sequence ", test_seq_s}, UVM_MEDIUM)
  endtask
endclass : dv_base_test
