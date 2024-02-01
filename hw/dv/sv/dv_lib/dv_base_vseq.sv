// Copyright lowRISC contributors (OpenTitan project).
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
  bit do_wait_for_reset = 1'b0;

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
    if (do_apply_reset) begin
      apply_reset(reset_kind);
      post_apply_reset(reset_kind);
    end else if (do_wait_for_reset) wait_for_reset(reset_kind);
    // delay after reset for tl agent check seq_item_port empty
    #1ps;
  endtask

  virtual task apply_reset(string kind = "HARD");
    if (kind == "HARD") begin
      if (cfg.clk_rst_vifs.size() > 0) begin
        fork
          begin : isolation_fork
            foreach (cfg.clk_rst_vifs[i]) begin
              automatic string ral_name = i;
              fork
                cfg.clk_rst_vifs[ral_name].apply_reset();
              join_none
            end
            wait fork;
          end : isolation_fork
        join
      end else begin // no ral model and only has default clk_rst_vif
        cfg.clk_rst_vif.apply_reset();
      end
    end // if (kind == "HARD")
  endtask

  // Apply all resets in the DUT concurrently to generate a random in-test reset scenario.
  //
  // - Assert resets concurrently to make sure all resets are issued.
  // - Deassert resets concurrently is a specific requirement of the `stress_all_with_rand_reset`
  // sequence, which will randomly issue resets and terminate the parallel sequence once all DUT
  // resets are deasserted. If DUT resets are deasserted at different time, the parallel sequence
  // might send a transaction request to driver between different resets are deasserting. Then when
  // `stress_all_with_rand_reset` sequence tries to terminate the parallel sequence, an UVM_ERROR
  // will be thrown by the sequencer saying `task responsible for requesting a wait_for_grant has
  // been killed`.
  // In order to ensure all resets at least being asserted for one clock cycle, this task takes an
  // optional input `reset_duration_ps` if the DUT has additional resets. The task uses this input
  // to compute the minimal time required to keep all resets asserted.
  virtual task apply_resets_concurrently(int reset_duration_ps = 0);

    // Has one or more RAL models in DUT.
    if (cfg.clk_rst_vifs.size() > 0) begin
      foreach (cfg.clk_rst_vifs[i]) begin
        cfg.clk_rst_vifs[i].drive_rst_pin(0);
        reset_duration_ps = max2(reset_duration_ps, cfg.clk_rst_vifs[i].clk_period_ps);
      end
      #(reset_duration_ps * $urandom_range(2, 10) * 1ps);
      foreach (cfg.clk_rst_vifs[i]) cfg.clk_rst_vifs[i].drive_rst_pin(1);

    // No RAL model and only has default clk_rst_vif.
    end else begin
      cfg.clk_rst_vif.drive_rst_pin(0);
      reset_duration_ps = max2(reset_duration_ps, cfg.clk_rst_vif.clk_period_ps);
      #(reset_duration_ps * $urandom_range(2, 10) * 1ps);
      cfg.clk_rst_vif.drive_rst_pin(1);
    end
  endtask

  // This is called after apply_reset in this class and after apply_resets_concurrently
  // in cip_base_vseq::run_seq_with_rand_reset_vseq.
  virtual task post_apply_reset(string reset_kind = "HARD");
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

  // wrapper task around run_csr_vseq - the purpose is to be able to call this directly for actual
  // csr tests (as opposed to higher level stress test that could also run csr seq as a fork by
  // calling run_csr_vseq(..) task)
  virtual task run_csr_vseq_wrapper(int num_times = 1, dv_base_reg_block models[$] = {});
    string        csr_test_type;

    // Env needs to have a ral instance.
    if (models.size() == 0) begin
      `DV_CHECK_GE_FATAL(cfg.ral_models.size(), 1)
    end

    // Get csr_test_type from plusarg
    void'($value$plusargs("csr_%0s", csr_test_type));

    // run the csr seq
    for (int i = 1; i <= num_times; i++) begin
      `uvm_info(`gfn, $sformatf("Running csr %0s vseq iteration %0d/%0d.",
                                csr_test_type, i, num_times), UVM_LOW)
      run_csr_vseq(.csr_test_type(csr_test_type), .models(models));
    end
  endtask

  // capture the entire csr seq as a task that can be overridden if desired
  // arg csr_test_type: what csr test to run {hw_reset, rw, bit_bash, aliasing}
  // arg num_test_csrs:instead of testing the entire ral model or passing test chunk info via
  // plusarg, provide ability to set a random number of csrs to test from higher level sequence
  // `models` is the list of RAL models to run the common sequences on.
  // `ral_name` is the string name of the RAL to run the common sequences on.
  // Both of these inputs are 'null' by default. If externally set, `models` takes precedence over
  // `ral_name`.
  virtual task run_csr_vseq(string csr_test_type,
                            int    num_test_csrs = 0,
                            bit    do_rand_wr_and_reset = 1,
                            dv_base_reg_block models[$] = {},
                            string ral_name = "");
    csr_base_seq m_csr_seq;

    // env needs to have at least one ral instance
    `DV_CHECK_GE_FATAL(cfg.ral_models.size(), 1)

    // Filter out the RAL blocks under test with the supplied name, if available.
    if (models.size() == 0) begin
      if (ral_name != "") begin
        `DV_CHECK_FATAL(cfg.ral_models.exists(ral_name))
        models.push_back(cfg.ral_models[ral_name]);
      end else begin
        foreach (cfg.ral_models[i]) models.push_back(cfg.ral_models[i]);
      end
    end

    // check which csr test type
    case (csr_test_type)
      "hw_reset": csr_base_seq::type_id::set_type_override(csr_hw_reset_seq::get_type());
      "rw"      : csr_base_seq::type_id::set_type_override(csr_rw_seq::get_type());
      "bit_bash": csr_base_seq::type_id::set_type_override(csr_bit_bash_seq::get_type());
      "aliasing": csr_base_seq::type_id::set_type_override(csr_aliasing_seq::get_type());
      "mem_walk": csr_base_seq::type_id::set_type_override(csr_mem_walk_seq::get_type());
      default   : `uvm_fatal(`gfn, $sformatf("specified opt is invalid: +csr_%0s", csr_test_type))
    endcase

    // Print the list of available exclusions that are in effect for debug.
    foreach (models[i]) begin
      csr_excl_item csr_excl = csr_utils_pkg::get_excl_item(models[i]);
      if (csr_excl != null) csr_excl.print_exclusions();
    end

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
      m_csr_write_seq.models = models;
      m_csr_write_seq.external_checker = cfg.en_scb;
      m_csr_write_seq.en_rand_backdoor_write = 1'b1;
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
    m_csr_seq.models = models;
    m_csr_seq.external_checker = cfg.en_scb;
    m_csr_seq.num_test_csrs = num_test_csrs;
    m_csr_seq.start(null);
  endtask

  // enable/disable csr_assert
  virtual function void set_csr_assert_en(bit enable, string path = "*");
    uvm_config_db#(bit)::set(null, path, "csr_assert_en", enable);
  endfunction

endclass
