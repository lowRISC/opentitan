// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test cs_cmd_req_done, cs_entropy_req, cs_hw_inst_exc and cs_fatal_err interrupts
// fired as expected

class csrng_intr_vseq extends csrng_base_vseq;
  `uvm_object_utils(csrng_intr_vseq)

  `uvm_object_new

  csrng_item   cs_item;
  string       path1, path2, path3, path4, path_push, path_full, path_pop, path_not_empty, path;
  bit [31:0]   backdoor_err_code_val;

  task release_ack_and_ack_sts(int inst_idx);
    string path_ack, path_ack_sts;

    // Get paths
    path_ack = $sformatf("tb.dut.u_csrng_core.cmd_stage_ack[%0d]", inst_idx);
    path_ack_sts = "tb.dut.u_csrng_core.cmd_stage_ack_sts";

    // Release signals
    if (!uvm_hdl_release(path_ack)) begin
      `uvm_error(`gfn, $sformatf("Path %s could not be released", path_ack))
    end
    if (!uvm_hdl_release(path_ack_sts)) begin
      `uvm_error(`gfn, $sformatf("Path %s could not be released", path_ack_sts))
    end
  endtask

  task test_cs_cmd_req_done();
    cs_item = csrng_item::type_id::create("cs_item");

    // Write CSRNG Cmd_Req - Instantiate Command
    cs_item.acmd  = csrng_pkg::INS;
    cs_item.clen  = 'h0;
    cs_item.flags = MuBi4True;
    cs_item.glen  = 'h0;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(SW_APP, cs_item);

    // Write CSRNG Cmd_Req Register - Generate Command
    cs_item.acmd  = csrng_pkg::GEN;
    cs_item.clen  = 'h0;
    cs_item.flags = MuBi4True;
    cs_item.glen  = 'h1;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(SW_APP, cs_item);

    // Write CSRNG Cmd_Req Register - Uninstantiate Command
    cs_item.acmd  = csrng_pkg::UNI;
    cs_item.clen  = 'h0;
    cs_item.flags = MuBi4True;
    cs_item.glen  = 'h0;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(SW_APP, cs_item);
  endtask // test_cs_cmd_req_done

  task test_cs_entropy_req();
    cs_item = csrng_item::type_id::create("cs_item");

    // Write CSRNG Cmd_Req - Instantiate Command
    cs_item.acmd  = csrng_pkg::INS;
    cs_item.clen  = 'h0;
    cs_item.flags = MuBi4False;
    cs_item.glen  = 'h0;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(SW_APP, cs_item);

    // Write CSRNG Cmd_Req Register - Generate Command
    cs_item.acmd  = csrng_pkg::GEN;
    cs_item.clen  = 'h0;
    cs_item.flags = MuBi4False;
    cs_item.glen  = 'h1;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(SW_APP, cs_item);

    // Expect/Clear interrupt bit
    csr_rd_check(.ptr(ral.intr_state.cs_entropy_req), .compare_value(1'b1));
    check_interrupts(.interrupts((1 << EntropyReq)), .check_set(1'b1));
    cfg.clk_rst_vif.wait_clks(100);
    // Make sure the interrupt bit is cleared
    csr_rd_check(.ptr(ral.intr_state.cs_entropy_req), .compare_value(1'b0));

    // Write CSRNG Cmd_Req Register - Uninstantiate Command
    cs_item.acmd  = csrng_pkg::UNI;
    cs_item.clen  = 'h0;
    cs_item.flags = MuBi4True;
    cs_item.glen  = 'h0;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(SW_APP, cs_item);
  endtask // test_cs_entropy_req

  task trigger_invalid_acmd_sts_err(uint app);
    // Write an invalid command and expect the corresponding status response.
    cs_item.randomize();
    cs_item.clen  = 'h0;
    cs_item.acmd  = cfg.which_invalid_acmd;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(app, cs_item, .exp_sts(CMD_STS_INVALID_ACMD));

    if (app != SW_APP) begin
      // Expect/Clear interrupt bit
      check_interrupts(.interrupts((1 << HwInstExc)), .check_set(1'b1));
      cfg.clk_rst_vif.wait_clks(100);
      // Make sure the interrupt bit is cleared
      csr_rd_check(.ptr(ral.intr_state.cs_hw_inst_exc), .compare_value(1'b0));
    end

    csr_rd(.ptr(ral.err_code), .value(backdoor_err_code_val));
    cov_vif.cg_err_code_sample(.err_code(backdoor_err_code_val));
  endtask // trigger_invalid_acmd_sts_err

  task trigger_invalid_seq_sts_err(uint app);
    // Write an invalid sequence of commands and expect the corresponding status response.
    if (cfg.which_cmd_inv_seq == INS) begin
      cs_item.randomize();
      cs_item.acmd  = cfg.which_cmd_inv_seq;
      `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
      send_cmd_req(app, cs_item);
    end

    cs_item.randomize();
    cs_item.acmd  = cfg.which_cmd_inv_seq;
    cs_item.clen  = 'h0;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(app, cs_item, .exp_sts(CMD_STS_INVALID_CMD_SEQ), .await_genbits(0));

    if (app != SW_APP) begin
      // Expect/Clear interrupt bit
      check_interrupts(.interrupts((1 << HwInstExc)), .check_set(1'b1));
      cfg.clk_rst_vif.wait_clks(100);
      // Make sure the interrupt bit is cleared
      csr_rd_check(.ptr(ral.intr_state.cs_hw_inst_exc), .compare_value(1'b0));
    end

    csr_rd(.ptr(ral.err_code), .value(backdoor_err_code_val));
    cov_vif.cg_err_code_sample(.err_code(backdoor_err_code_val));
  endtask // trigger_invalid_seq_sts_err

  task trigger_reseed_interval_sts_err(uint app);
    // Send cfg.reseed_interval + 1 generate commands and expect the corresponding status response.
    csr_wr(.ptr(ral.reseed_interval), .value(cfg.reseed_interval));

    if (cfg.which_cmd_inv_seq != INS) begin
      cs_item.randomize();
      cs_item.acmd  = INS;
      `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
      send_cmd_req(app, cs_item);
    end
    `uvm_info(`gfn, $sformatf("Setting the reseed interval to %d", cfg.reseed_interval), UVM_DEBUG)
    for (int i = 0; i < cfg.reseed_interval; i++) begin
      cs_item.randomize();
      cs_item.acmd  = GEN;
      cs_item.glen  = 'h1;
      `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
      send_cmd_req(app, cs_item);
    end
    cs_item.randomize();
    cs_item.acmd  = GEN;
    cs_item.glen  = 'h1;
    cs_item.clen  = 'h0;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(app, cs_item, .exp_sts(CMD_STS_RESEED_CNT_EXCEEDED), .await_genbits(0));

    if (app != SW_APP) begin
      // Expect/Clear interrupt bit
      check_interrupts(.interrupts((1 << HwInstExc)), .check_set(1'b1));
      cfg.clk_rst_vif.wait_clks(100);
      // Make sure the interrupt bit is cleared
      csr_rd_check(.ptr(ral.intr_state.cs_hw_inst_exc), .compare_value(1'b0));
    end

    csr_rd(.ptr(ral.err_code), .value(backdoor_err_code_val));
    cov_vif.cg_err_code_sample(.err_code(backdoor_err_code_val));
  endtask // trigger_reseed_interval_sts_err

  task test_cmd_sts_errs(uint app);
    trigger_invalid_acmd_sts_err(app);
    trigger_invalid_seq_sts_err(app);
    trigger_reseed_interval_sts_err(app);

    ral.ctrl.enable.set(prim_mubi_pkg::MuBi4False);
    csr_update(.csr(ral.ctrl));
    cfg.clk_rst_vif.wait_clks(100);
    ral.ctrl.enable.set(prim_mubi_pkg::MuBi4True);
    csr_update(.csr(ral.ctrl));
  endtask // test_cmd_sts_errs

  task test_cs_fatal_err();
    string        path, path1, path2;
    bit           value1, value2;
    bit [7:0]     value3;
    bit [3:0]     value4;
    string        fifo_name, fld_name;
    int           first_index, last_index;
    string        fifo_base_path;
    string        path_exts [6] = {"push", "full", "wdata", "pop", "not_empty", "rdata"};
    string        fifo_forced_paths [6];
    bit           fifo_forced_values [6] = {1'b1, 1'b1, 1'b0, 1'b1, 1'b0, 1'b0};
    string        fifo_err_path [2][string];
    bit           fifo_err_value [2][string];
    string        path_key;

    fifo_err_path[0] = '{"write": "push", "read": "pop", "state": "full"};
    fifo_err_path[1] = '{"write": "full", "read": "not_empty", "state": "not_empty"};
    fifo_err_value[0] = '{"write": 1'b1, "read": 1'b1, "state": 1'b1};
    fifo_err_value[1] = '{"write": 1'b1, "read": 1'b0, "state": 1'b0};

    // Turn off some SVAs which are likely triggering when injecting fatal errors.
    `define CMD_STAGE_0 tb.dut.u_csrng_core.gen_cmd_stage[0].u_csrng_cmd_stage
    `define CMD_STAGE_1 tb.dut.u_csrng_core.gen_cmd_stage[1].u_csrng_cmd_stage
    `define CMD_STAGE_2 tb.dut.u_csrng_core.gen_cmd_stage[2].u_csrng_cmd_stage
    `define HIER_PATH(prefix, suffix) `"prefix.suffix`"
    $assertoff(0, `HIER_PATH(`CMD_STAGE_0, CsrngCmdStageGenbitsFifoPushExpected_A));
    $assertoff(0, `HIER_PATH(`CMD_STAGE_1, CsrngCmdStageGenbitsFifoPushExpected_A));
    $assertoff(0, `HIER_PATH(`CMD_STAGE_2, CsrngCmdStageGenbitsFifoPushExpected_A));

    // Enable CSRNG
    ral.ctrl.enable.set(prim_mubi_pkg::MuBi4True);
    csr_update(.csr(ral.ctrl));
    // Enable intr_state
    csr_wr(.ptr(ral.intr_enable), .value(32'd15));

    fld_name = cfg.which_fatal_err.name();

    first_index = find_index("_", fld_name, "first");
    last_index = find_index("_", fld_name, "last");

    case (cfg.which_fatal_err) inside
      sfifo_cmd_error, sfifo_genbits_error, sfifo_cmdreq_error, sfifo_rcstage_error,
      sfifo_keyvrc_error, sfifo_bencreq_error, sfifo_final_error, sfifo_gbencack_error,
      sfifo_grcstage_error, sfifo_gadstage_error, sfifo_ggenbits_error,
      sfifo_blkenc_error, sfifo_updreq_error, sfifo_bencack_error, sfifo_pdata_error,
      sfifo_ggenreq_error: begin
        fifo_base_path = fld_name.substr(0, last_index-1);

        foreach (path_exts[i]) begin
          fifo_forced_paths[i] = cfg.csrng_path_vif.fifo_err_path(cfg.NHwApps, fifo_base_path,
                                                                  path_exts[i]);
        end
        if (cfg.which_fatal_err == sfifo_updreq_error ||
            cfg.which_fatal_err == sfifo_bencack_error ||
            cfg.which_fatal_err == sfifo_pdata_error ||
            cfg.which_fatal_err == sfifo_ggenreq_error) begin
          force_all_fifo_errs_exception(fifo_forced_paths, fifo_forced_values, path_exts,
                                        ral.intr_state.cs_fatal_err, 1'b1, cfg.which_fifo_err);
        end else begin
          force_all_fifo_errs(fifo_forced_paths, fifo_forced_values, path_exts,
                              ral.intr_state.cs_fatal_err, 1'b1, cfg.which_fifo_err);
        end
      end
      cmd_stage_sm_error, main_sm_error, drbg_gen_sm_error, drbg_updbe_sm_error,
      drbg_updob_sm_error: begin
        path = cfg.csrng_path_vif.sm_err_path(fld_name.substr(0, last_index-1), cfg.NHwApps);
        force_path_err(path, 8'b0, ral.intr_state.cs_fatal_err, 1'b1);
      end
      aes_cipher_sm_error: begin
        // Get the path to the AES cipher core FSM. We need it in any case to test that AES enters
        // the terminal error state.
        string aes_fsm_path;
        logic [aes_pkg::CipherCtrlStateWidth-1:0] aes_fsm_state;
        if (aes_pkg::SP2V_LOGIC_HIGH[cfg.which_sp2v] == 1'b1) begin
          aes_fsm_path = cfg.csrng_path_vif.aes_cipher_fsm_err_path(cfg.which_sp2v, "p");
        end else begin
          aes_fsm_path = cfg.csrng_path_vif.aes_cipher_fsm_err_path(cfg.which_sp2v, "n");
        end
        case (cfg.which_aes_cm) inside
          fsm_sparse, fsm_redun: begin
            if (cfg.which_aes_cm == fsm_sparse) begin
              // Force an invalid state encoding.
              value3 = 8'b0;
            end else begin
              // Force a valid state encoding. We take a state in which the FSM is just for one
              // clock cycle to ensure it's detected no matter what the DUT is actually doing,
              // i.e., whether it is idle or stalled.
              value3 = {2'b00, {aes_pkg::CIPHER_CTRL_CLEAR_S}};
            end
            force_path_err(aes_fsm_path, value3, ral.intr_state.cs_fatal_err, 1'b1);
          end
          ctrl_sparse: begin
            // We force one rail of one of the mux control signals to another valid encoding.
            value3 = {3'b000, {aes_pkg::ADD_RK_INIT}};
            if (aes_pkg::SP2V_LOGIC_HIGH[cfg.which_sp2v] == 1'b1) begin
              path = cfg.csrng_path_vif.aes_cipher_ctrl_err_path(cfg.which_sp2v, "p");
              force_path_err(path, value3, ral.intr_state.cs_fatal_err, 1'b1);
            end else begin
              path = cfg.csrng_path_vif.aes_cipher_ctrl_err_path(cfg.which_sp2v, "n");
              force_path_err(path, value3, ral.intr_state.cs_fatal_err, 1'b1);
            end
          end
          ctr_redun: begin
            value4 = 4'hf;
            if (aes_pkg::SP2V_LOGIC_HIGH[cfg.which_sp2v] == 1'b1) begin
              path = cfg.csrng_path_vif.aes_cipher_rnd_ctr_err_path(cfg.which_sp2v, "p");
              force_path_err(path, value4, ral.intr_state.cs_fatal_err, 1'b1);
            end else begin
              path = cfg.csrng_path_vif.aes_cipher_rnd_ctr_err_path(cfg.which_sp2v, "n");
              force_path_err(path, value4, ral.intr_state.cs_fatal_err, 1'b1);
            end
          end
        endcase
        // Check that the AES cipher core FSM has entered the terminal error state.
        `DV_CHECK(uvm_hdl_read(aes_fsm_path, aes_fsm_state))
        `DV_CHECK_EQ(aes_fsm_state, aes_pkg::CIPHER_CTRL_ERROR)
      end
      cmd_gen_cnt_error: begin
        path = cfg.csrng_path_vif.cmd_gen_cnt_err_path(cfg.NHwApps);
        force_path_err(path, 8'h01, ral.intr_state.cs_fatal_err, 1'b1);
      end
      fifo_write_error, fifo_read_error, fifo_state_error: begin
        fifo_name = cfg.which_fifo.name();
        path_key = fld_name.substr(first_index+1, last_index-1);

        path1 = cfg.csrng_path_vif.fifo_err_path(cfg.NHwApps, fifo_name,
                                                 fifo_err_path[0][path_key]);
        path2 = cfg.csrng_path_vif.fifo_err_path(cfg.NHwApps, fifo_name,
                                                 fifo_err_path[1][path_key]);
        value1 = fifo_err_value[0][path_key];
        value2 = fifo_err_value[1][path_key];

        if (cfg.which_fatal_err == fifo_read_error &&
           ((cfg.which_fifo == sfifo_ggenreq) || (cfg.which_fifo == sfifo_pdata) ||
            (cfg.which_fifo == sfifo_bencack) || (cfg.which_fifo == sfifo_updreq)))
        begin
          force_fifo_err_exception(path1, path2, 1'b1, 1'b0, 1'b0, ral.intr_state.cs_fatal_err,
                                   1'b1);
        end else begin
          force_fifo_err(path1, path2, value1, value2, ral.intr_state.cs_fatal_err, 1'b1);
        end
      end
      default: begin
        `uvm_fatal(`gfn, "Invalid case! (bug in environment)")
      end
    endcase // case (cfg.which_fatal_err)
    csr_rd(.ptr(ral.err_code), .value(backdoor_err_code_val));
    cov_vif.cg_err_code_sample(.err_code(backdoor_err_code_val));

    // Turn SVAs back on.
    $asserton(0, `HIER_PATH(`CMD_STAGE_0, CsrngCmdStageGenbitsFifoPushExpected_A));
    $asserton(0, `HIER_PATH(`CMD_STAGE_1, CsrngCmdStageGenbitsFifoPushExpected_A));
    $asserton(0, `HIER_PATH(`CMD_STAGE_2, CsrngCmdStageGenbitsFifoPushExpected_A));
    `undef CMD_STAGE_0
    `undef CMD_STAGE_1
    `undef CMD_STAGE_2
    `undef HIER_PATH

  endtask // test_cs_fatal_err

  task body();
    super.body();
    // Create EDN host sequences.
    for (int i = 0; i < NUM_HW_APPS; i++) begin
      m_edn_push_seq[i] = push_pull_host_seq#(csrng_pkg::CSRNG_CMD_WIDTH)::type_id::create
                                              ($sformatf("m_edn_push_seq[%0d]", i));
    end

    // Turn off fatal alert check
    expect_fatal_alerts = 1'b1;

    // Turn off assertions
    $assertoff(0, "tb.entropy_src_if.ReqHighUntilAck_A");
    $assertoff(0, "tb.entropy_src_if.AckAssertedOnlyWhenReqAsserted_A");
    $assertoff(0, "tb.dut.u_csrng_core.u_prim_arbiter_ppc_updblk_arb.LockArbDecision_A");
    $assertoff(0, "tb.dut.u_csrng_core.u_prim_arbiter_ppc_benblk_arb.ReqStaysHighUntilGranted0_M");
    $assertoff(0, "tb.dut.u_csrng_core.u_prim_arbiter_ppc_updblk_arb.ReqStaysHighUntilGranted0_M");
    cfg.csrng_assert_vif.assert_off();
    `DV_ASSERT_CTRL_REQ("CmdStageFifoAsserts", 0)

    // Test cs_cmd_req_done interrupt
    // cs_cmd_req_done interrupt is checked in the send_cmd_req()
    test_cs_cmd_req_done();

    // Test cs_entropy_req interrupt
    test_cs_entropy_req();

    // Test the command status response errors and for the HW apps
    // the cs_hw_inst_exc interrupt.
    for (int app = 0; app <= SW_APP; app++) begin
      test_cmd_sts_errs(app);
    end

    // Test cs_fatal_err interrupt
    test_cs_fatal_err();

    cfg.clk_rst_vif.wait_clks(50);
    // Clear intr_enable
    csr_wr(.ptr(ral.intr_enable), .value(32'h0));
    ral.ctrl.enable.set(prim_mubi_pkg::MuBi4False);
    ral.ctrl.sw_app_enable.set(prim_mubi_pkg::MuBi4True);
    csr_update(.csr(ral.ctrl));
    // Clear intr_state
    csr_wr(.ptr(ral.intr_state), .value(32'd15));
    cfg.clk_rst_vif.wait_clks(100);

    if (cfg.which_fatal_err inside {cmd_stage_sm_err, main_sm_err,
                                    drbg_gen_sm_err, drbg_updbe_sm_err, drbg_updob_sm_err,
                                    aes_cipher_sm_err,
                                    cmd_gen_cnt_err, cmd_gen_cnt_err_test}) begin
      // These errors are either not gated with the module enable or they cause the main FSM to
      // escalate of which the alert output itself isn't gated with the module enable. After
      // clearing the interrupt state register, the cs_fatal_err interrupt bit again gets asserted.
      // The interrupt enable just affetcs the signaling of the actual interrupt.
      csr_rd_check(.ptr(ral.intr_state), .compare_value(4'b1000));
    end else begin
      // These errors are gated with the module enable. As the module has been switched off now,
      // these are not expected to re-propagate into the interrupt state register after clearing.
      csr_rd_check(.ptr(ral.intr_state), .compare_value(4'b0));
    end

    // Turn assertions back on
    $asserton(0, "tb.entropy_src_if.ReqHighUntilAck_A");
    $asserton(0, "tb.entropy_src_if.AckAssertedOnlyWhenReqAsserted_A");
    $asserton(0, "tb.dut.u_csrng_core.u_prim_arbiter_ppc_updblk_arb.LockArbDecision_A");
    $asserton(0, "tb.dut.u_csrng_core.u_prim_arbiter_ppc_benblk_arb.ReqStaysHighUntilGranted0_M");
    $asserton(0, "tb.dut.u_csrng_core.u_prim_arbiter_ppc_updblk_arb.ReqStaysHighUntilGranted0_M");
    cfg.csrng_assert_vif.assert_on();

  endtask : body

endclass : csrng_intr_vseq
