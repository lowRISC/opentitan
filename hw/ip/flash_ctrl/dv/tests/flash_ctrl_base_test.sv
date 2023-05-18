// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_base_test #(
    type CFG_T = flash_ctrl_env_cfg,
    type ENV_T = flash_ctrl_env
  ) extends cip_base_test #(
    .CFG_T(CFG_T),
    .ENV_T(ENV_T)
  );

  // A prototype for the registry to associate the parameterized base test
  // with the name 'flash_ctrl_base_test'
  //
  // Register the name 'flash_ctrl_base_test' with the UVM factory to be associated
  // with the template base test class parameterized with the default types (see
  // declaration. We cannot invoke the standard UVM factory automation macro t
  // (uvm_component_param_utils) to register a parameterized test class with the
  // factory because the creation of the test by name (via the UVM_TESTNAME
  // plusarg) does not work. We expand the contents of the automation macro
  // here instead. See the following paper for details:
  // https://verificationacademy-news.s3.amazonaws.com/DVCon2016/Papers/
  // dvcon-2016_paramaters-uvm-coverage-and-emulation-take-two-and-call-me-in-the-morning_paper.pdf
  typedef uvm_component_registry#(flash_ctrl_base_test#(CFG_T, ENV_T),
                                  "flash_ctrl_base_test") type_id;

  // functions to support the component registry above
  static function type_id get_type();
    return type_id::get();
  endfunction : get_type

  virtual function uvm_object_wrapper get_object_type();
    return type_id::get();
  endfunction : get_object_type

  const static string type_name = "flash_ctrl_base_test";

  virtual function string get_type_name();
    return type_name;
  endfunction : get_type_name

  `uvm_component_new
  int run_cnt = 1;
  // the base class dv_base_test creates the following instances:
  // flash_ctrl_env_cfg: cfg
  // flash_ctrl_env:     env

  // the base class also looks up UVM_TEST_SEQ plusarg to create and run that seq in
  // the run_phase; as such, nothing more needs to be done

  // Add flash_ctrl only plusarg
  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
     // Knob to use small page rma
    void'($value$plusargs("en_small_rma=%0b", cfg.en_small_rma));
    void'($value$plusargs("scb_otf_en=%0b", cfg.scb_otf_en));
    void'($value$plusargs("multi_alert=%0b", cfg.multi_alert_en));
    void'($value$plusargs("ecc_mode=%0d", cfg.ecc_mode));
    void'($value$plusargs("serr_pct=%0d", cfg.serr_pct));
    void'($value$plusargs("derr_pct=%0d", cfg.derr_pct));
    void'($value$plusargs("ierr_pct=%0d", cfg.ierr_pct));
    void'($value$plusargs("otf_num_rw=%0d", cfg.otf_num_rw));
    void'($value$plusargs("otf_num_hr=%0d", cfg.otf_num_hr));
    void'($value$plusargs("otf_wr_pct=%0d", cfg.otf_wr_pct));
    void'($value$plusargs("otf_rd_pct=%0d", cfg.otf_rd_pct));
    void'($value$plusargs("en_always_all=%0d", cfg.en_always_all));
    void'($value$plusargs("en_always_read=%0d", cfg.en_always_read));
    void'($value$plusargs("en_always_erase=%0d", cfg.en_always_erase));
    void'($value$plusargs("en_always_prog=%0d", cfg.en_always_prog));
    void'($value$plusargs("en_all_info_acc=%0d", cfg.en_all_info_acc));
    void'($value$plusargs("rd_buf_en_to=%0d", cfg.wait_rd_buf_en_timeout_ns));
    if (cfg.en_always_all) begin
      cfg.en_always_read = 1;
      cfg.en_always_prog = 1;
      cfg.en_always_erase = 1;
    end
    cfg.en_always_any = (cfg.en_always_read | cfg.en_always_erase |
                         cfg.en_always_prog);
  endfunction

  task run_phase(uvm_phase phase);
    int dbg_run_cnt = 0;
    if ($value$plusargs("rerun=%0d", run_cnt)) begin
      `uvm_info("TEST", $sformatf("run_cnt is set to %0d", run_cnt), UVM_LOW)
    end
    phase.raise_objection(this);
    run_test_seq = 0;
    super.run_phase(phase);

    repeat(run_cnt) begin
      run_seq(test_seq_s, phase);
      if (run_cnt > 1) begin
        env.virtual_sequencer.stop_sequences();
        `uvm_info("Test", $sformatf("TESTEND %0d",++dbg_run_cnt), UVM_MEDIUM)
        foreach (env.m_tl_agents[i]) env.m_tl_agents[i].monitor.pending_a_req.delete();
      end
    end
    phase.drop_objection(this);

  endtask // run_phase
endclass : flash_ctrl_base_test
