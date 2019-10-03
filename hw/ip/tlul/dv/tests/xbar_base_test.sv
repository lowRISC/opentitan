// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TODO(taliu) extend this class with the common base test
class xbar_base_test extends uvm_test;

  xbar_env        env;
  xbar_env_cfg    cfg;
  virtual clk_if  clk_vif;
  xbar_vseq       vseq;
  int unsigned    max_quit_count = 10;
  int unsigned    test_timeout_ns = 200_000_000; // 200ms
  int unsigned    drain_time_ns = 2_000;  // 2us

  `uvm_component_utils(xbar_base_test)

  function new(string name="", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(virtual clk_if)::get(null, "", "clk_if", clk_vif)) begin
      `uvm_fatal(get_full_name(), "Cannot get clk_if")
    end
    env = xbar_env::type_id::create("env", this);
    // Create environment config
    cfg = xbar_env_cfg::type_id::create("cfg");
    cfg.init_cfg();
    if (!cfg.randomize()) begin
      `uvm_fatal(get_full_name(), "Cannot randomizing cfg")
    end
    vseq = xbar_vseq::type_id::create("vseq");
    uvm_config_db#(xbar_env_cfg)::set(this, "*", "cfg", cfg);
  endfunction

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
    phase.raise_objection(this);
    tl_agent_pkg::enable_logging();
    run_seq();
    phase.drop_objection(this);
  endtask

  virtual task run_seq();
    `uvm_info(get_full_name(), "Start xbar_vseq...", UVM_LOW)
    if (!vseq.randomize()) begin
      `uvm_fatal(get_full_name(), "Cannot randomize xbar_vseq")
    end
    vseq.start(env.vseqr);
    `uvm_info(get_full_name(), "xbar_vseq...DONE", UVM_LOW)
  endtask

endclass
