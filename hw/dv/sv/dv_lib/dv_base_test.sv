// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dv_base_test #(type CFG_T = dv_base_env_cfg,
                     type ENV_T = dv_base_env) extends uvm_test;
  `uvm_component_param_utils(dv_base_test #(CFG_T, ENV_T))

  ENV_T             env;
  CFG_T             cfg;
  bit               run_test_seq = 1'b1;
  string            test_seq_s;

  uint   max_quit_count  = 1;
  uint64 test_timeout_ns = 200_000_000; // 200ms
  uint   drain_time_ns   = 2_000;  // 2us

  `uvm_component_new

  virtual function void build_phase(uvm_phase phase);
    dv_report_server m_dv_report_server = new();
    uvm_report_server::set_server(m_dv_report_server);

    super.build_phase(phase);

    env = ENV_T::type_id::create("env", this);
    cfg = CFG_T::type_id::create("cfg", this);
    // don't add args for initialize. Use default value instead
    cfg.initialize();
    `DV_CHECK_RANDOMIZE_FATAL(cfg)
    uvm_config_db#(CFG_T)::set(this, "env", "cfg", cfg);

    // knob to en/dis scb (enabled by default)
    void'($value$plusargs("en_scb=%0b", cfg.en_scb));
    // knob to cfg all agents with zero delays
    void'($value$plusargs("zero_delays=%0b", cfg.zero_delays));
  endfunction : build_phase

  virtual function void end_of_elaboration_phase(uvm_phase phase);
    super.end_of_elaboration_phase(phase);
    void'($value$plusargs("max_quit_count=%0d", max_quit_count));
    set_max_quit_count(max_quit_count);
    void'($value$plusargs("test_timeout_ns=%0d", test_timeout_ns));
    uvm_top.set_timeout((test_timeout_ns * 1ns));
  endfunction : end_of_elaboration_phase

  virtual task run_phase(uvm_phase phase);
    void'($value$plusargs("drain_time_ns=%0d", drain_time_ns));
    phase.phase_done.set_drain_time(this, (drain_time_ns * 1ns));
    void'($value$plusargs("UVM_TEST_SEQ=%0s", test_seq_s));
    if (run_test_seq) begin
      run_seq(test_seq_s, phase);
    end
    // TODO: add hook for end of test checking
  endtask : run_phase

  virtual task run_seq(string test_seq_s, uvm_phase phase);
    uvm_sequence test_seq = create_seq_by_name(test_seq_s);

    // provide virtual_sequencer earlier, so we may use the p_sequencer in constraint
    test_seq.set_sequencer(env.virtual_sequencer);
    `DV_CHECK_RANDOMIZE_FATAL(test_seq)

    `uvm_info(`gfn, {"Starting test sequence ", test_seq_s}, UVM_MEDIUM)
    phase.raise_objection(this, $sformatf("%s objection raised", `gn));
    test_seq.start(env.virtual_sequencer);
    phase.drop_objection(this, $sformatf("%s objection dropped", `gn));
    phase.phase_done.display_objections();
    `uvm_info(`gfn, {"Finished test sequence ", test_seq_s}, UVM_MEDIUM)
  endtask

  // TODO: add default report_phase implementation

endclass : dv_base_test


