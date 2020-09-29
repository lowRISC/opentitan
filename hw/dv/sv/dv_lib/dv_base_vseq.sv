// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dv_base_vseq #(type RAL_T               = dv_base_reg_block,
                     type CFG_T               = dv_base_env_cfg,
                     type COV_T               = dv_base_env_cov,
                     type VIRTUAL_SEQUENCER_T = dv_base_virtual_sequencer) extends uvm_sequence;
  `uvm_object_param_utils(dv_base_vseq #(RAL_T, CFG_T, COV_T, VIRTUAL_SEQUENCER_T))
  `uvm_declare_p_sequencer(VIRTUAL_SEQUENCER_T)

  // number of iterations to run the test seq - please override constraint in extended vseq
  // randomization for this is disabled in pre_start since we don't want to re-randomize it again
  rand uint num_trans;

  constraint num_trans_c {
    num_trans inside {[1:20]};
  }

  // handles for ease of op
  CFG_T   cfg;
  RAL_T   ral;
  COV_T   cov;

  // knobs to enable pre_start routines
  bit do_dut_init       = 1'b1;
  bit do_apply_reset    = 1'b1;
  bit do_wait_for_reset = 1'b1;

  // knobs to enable post_start routines
  bit do_dut_shutdown   = 1'b1;

  // various knobs to enable certain routines
  // this knob allows user to disable assertions in csr_hw_reset before random write sequence,
  // the assertions will turn back on after the hw reset deasserted
  bit enable_asserts_in_hw_reset_rand_wr  = 1'b1;

  `uvm_object_new

  virtual function void set_handles();
    `DV_CHECK_NE_FATAL(p_sequencer, null, "Did you forget to call `set_sequencer()`?")
    cfg = p_sequencer.cfg;
    cov = p_sequencer.cov;
    ral = cfg.ral;
  endfunction

  // This function is invoked in pre_randomize(). Override it in the extended classes to configure
  // / control the randomization of this sequence.
  virtual function void configure_vseq();
  endfunction

  function void pre_randomize();
    // Set the handles in pre_randomize(), so that the knobs in cfg are available during sequence
    // randomization. This forces `p_sequencer` handle to be set before the randomization - users
    // are required to call `set_sequencer()` right after creating the sequence and before
    // randomizing it.
    if (cfg == null) set_handles();
    configure_vseq();
  endfunction

  task pre_start();
    super.pre_start();
    if (cfg == null) set_handles();
    if (do_dut_init) dut_init("HARD");
    num_trans.rand_mode(0);
  endtask

  task body();
    `uvm_fatal(`gtn, "Need to override this when you extend from this class!")
  endtask : body

  task post_start();
    super.post_start();
    if (do_dut_shutdown) dut_shutdown();
  endtask

  /*
   * startup, reset and shutdown related tasks
   */
  virtual task dut_init(string reset_kind = "HARD");
    if (do_apply_reset)         apply_reset(reset_kind);
    else if (do_wait_for_reset) wait_for_reset(reset_kind);
    // delay after reset for tl agent check seq_item_port empty
    #1ps;
  endtask

  virtual task apply_reset(string kind = "HARD");
    if (kind == "HARD") begin
      csr_utils_pkg::reset_asserted();
      cfg.clk_rst_vif.apply_reset();
      csr_utils_pkg::clear_outstanding_access();
      csr_utils_pkg::reset_deasserted();
    end
    if (cfg.has_ral) begin
      foreach (cfg.ral_models[i]) cfg.ral_models[i].reset(kind);
    end
  endtask

  virtual task wait_for_reset(string reset_kind     = "HARD",
                              bit wait_for_assert   = 1,
                              bit wait_for_deassert = 1);
    if (wait_for_assert) begin
      `uvm_info(`gfn, "waiting for rst_n assertion...", UVM_MEDIUM)
      @(negedge cfg.clk_rst_vif.rst_n);
    end
    if (wait_for_deassert) begin
      `uvm_info(`gfn, "waiting for rst_n de-assertion...", UVM_MEDIUM)
      @(posedge cfg.clk_rst_vif.rst_n);
    end
    `uvm_info(`gfn, "wait_for_reset done", UVM_HIGH)
  endtask

  // dut shutdown - this is called in post_start if do_dut_shutdown bit is set
  virtual task dut_shutdown();
    csr_utils_pkg::wait_no_outstanding_access();
  endtask

  // function to add csr exclusions of the given type using the csr_excl_item item
  // arg csr_test_type: this the the type of csr test run - we may want additional exclusions
  // depending on what test seq we are running
  // arg csr_excl: this is the csr exclusion object that maintains the list of exclusions
  // the same object handle is to be passed to csr sequences in csr_seq_lib so that they can query
  // those exclusions
  virtual function void add_csr_exclusions(string           csr_test_type,
                                           csr_excl_item    csr_excl,
                                           string           scope = "ral");
    `uvm_info(`gfn, "no exclusion item added from this function", UVM_DEBUG)
  endfunction

  // TODO: temp support, can delete this once all IPs update their exclusion in hjson
  virtual function csr_excl_item add_and_return_csr_excl(string csr_test_type);
    add_csr_exclusions(csr_test_type, ral.csr_excl);
    ral.csr_excl.print_exclusions();
    return ral.csr_excl;
  endfunction

  // wrapper task around run_csr_vseq - the purpose is to be able to call this directly for actual
  // csr tests (as opposed to higher level stress test that could also run csr seq as a fork by
  // calling run_csr_vseq(..) task)
  virtual task run_csr_vseq_wrapper(int num_times = 1);
    string        csr_test_type;
    csr_excl_item csr_excl;

    // env needs to have a ral instance
    `DV_CHECK_EQ_FATAL(cfg.has_ral, 1'b1)

    // get csr_test_type from plusarg
    void'($value$plusargs("csr_%0s", csr_test_type));

    // create csr exclusions before running the csr seq
    csr_excl = add_and_return_csr_excl(csr_test_type);

    // run the csr seq
    for (int i = 1; i <= num_times; i++) begin
      `uvm_info(`gfn, $sformatf("running csr %0s vseq iteration %0d/%0d",
                                csr_test_type, i, num_times), UVM_LOW)
      run_csr_vseq(.csr_test_type(csr_test_type), .csr_excl(csr_excl));
    end
  endtask

  // capture the entire csr seq as a task that can be overridden if desired
  // arg csr_test_type: what csr test to run {hw_reset, rw, bit_bash, aliasing}
  // arg csr_excl: csr exclusion object - needs to be created and exclusions set before call
  // arg num_test_csrs:instead of testing the entire ral model or passing test chunk info via
  // plusarg, provide ability to set a random number of csrs to test from higher level sequence
  virtual task run_csr_vseq(string          csr_test_type = "",
                            csr_excl_item   csr_excl = null,
                            int             num_test_csrs = 0,
                            bit             do_rand_wr_and_reset = 1);
    csr_base_seq  m_csr_seq;

    // env needs to have a ral instance
    `DV_CHECK_EQ_FATAL(cfg.has_ral, 1'b1)

    // check which csr test type
    case (csr_test_type)
      "hw_reset": csr_base_seq::type_id::set_type_override(csr_hw_reset_seq::get_type());
      "rw"      : csr_base_seq::type_id::set_type_override(csr_rw_seq::get_type());
      "bit_bash": csr_base_seq::type_id::set_type_override(csr_bit_bash_seq::get_type());
      "aliasing": csr_base_seq::type_id::set_type_override(csr_aliasing_seq::get_type());
      "mem_walk": csr_base_seq::type_id::set_type_override(csr_mem_walk_seq::get_type());
      default   : `uvm_fatal(`gfn, $sformatf("specified opt is invalid: +csr_%0s", csr_test_type))
    endcase

    // if hw_reset test, then write all CSRs first and reset the whole dut
    if (csr_test_type == "hw_reset" && do_rand_wr_and_reset) begin
      string        reset_type = "HARD";
      csr_write_seq m_csr_write_seq;

      // Writing random values to CSRs might trigger assertion errors. So we disable in the entire
      // DUT hierarchy and re-enable after resetting the DUT. See DV_ASSERT_CTRL macro defined in
      // hw/dv/sv/dv_utils/dv_macros.svh for more details.
      if (!enable_asserts_in_hw_reset_rand_wr) begin
        `DV_ASSERT_CTRL_REQ("dut_assert_en", 1'b0)
      end

      // run write-only sequence to randomize the csr values
      m_csr_write_seq = csr_write_seq::type_id::create("m_csr_write_seq");
      m_csr_write_seq.models = cfg.ral_models;
      m_csr_write_seq.external_checker = cfg.en_scb;
      m_csr_write_seq.en_rand_backdoor_write = 1'b1;
      m_csr_write_seq.set_csr_excl_item(csr_excl);
      m_csr_write_seq.start(null);

      // run dut_shutdown before asserting reset
      dut_shutdown();
      // issue reset
      void'($value$plusargs("do_reset=%0s", reset_type));
      dut_init(reset_type);
      if (!enable_asserts_in_hw_reset_rand_wr) begin
        `DV_ASSERT_CTRL_REQ("dut_assert_en", 1'b1)
      end
    end

    // create base csr seq and pass our ral
    m_csr_seq = csr_base_seq::type_id::create("m_csr_seq");
    m_csr_seq.models = cfg.ral_models;
    m_csr_seq.external_checker = cfg.en_scb;
    m_csr_seq.num_test_csrs = num_test_csrs;
    m_csr_seq.set_csr_excl_item(csr_excl);
    m_csr_seq.start(null);
  endtask

  // enable/disable csr_assert
  virtual function void set_csr_assert_en(bit enable, string path = "*");
    uvm_config_db#(bit)::set(null, path, "csr_assert_en", enable);
  endfunction

endclass
