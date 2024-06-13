// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test ERR_CODE fields fired as expected, as well as ERR_CODE_TEST register

class csrng_err_vseq extends csrng_base_vseq;
  `uvm_object_utils(csrng_err_vseq)

  `uvm_object_new

  csrng_item   cs_item;

  task body();
    bit [4:0]     err_code_test_bit;
    string        path, path1, path2, path3;
    bit           value1, value2;
    bit [7:0]     value3;
    bit [3:0]     value4;
    string        fifo_name;
    int           first_index, last_index;
    string        fifo_base_path;
    string        path_exts [6] = {"push", "full", "wdata", "pop", "not_empty", "rdata"};
    string        fifo_forced_paths [6];
    bit           fifo_forced_values [6] = {1'b1, 1'b1, 1'b0, 1'b1, 1'b0, 1'b0};
    string        fifo_err_path [2][string];
    bit           fifo_err_value [2][string];
    string        path_key;
    string        reg_name, fld_name;
    uvm_reg       csr;
    uvm_reg_field fld;
    bit [31:0]    backdoor_err_code_val;

    super.body();

    fifo_err_path[0] = '{"write": "push", "read": "pop", "state": "full"};
    fifo_err_path[1] = '{"write": "full", "read": "not_empty", "state": "not_empty"};
    fifo_err_value[0] = '{"write": 1'b1, "read": 1'b1, "state": 1'b1};
    fifo_err_value[1] = '{"write": 1'b1, "read": 1'b0, "state": 1'b0};

    // Create edn host sequences
    for (int i = 0; i < NUM_HW_APPS; i++) begin
      m_edn_push_seq[i] = push_pull_host_seq#(csrng_pkg::CSRNG_CMD_WIDTH)::type_id::create
                                              ($sformatf("m_edn_push_seq[%0d]", i));
    end

    // Turn off fatal alert check
    expect_fatal_alerts = 1'b1;

    `define CMD_STAGE_0 tb.dut.u_csrng_core.gen_cmd_stage[0].u_csrng_cmd_stage
    `define CMD_STAGE_1 tb.dut.u_csrng_core.gen_cmd_stage[1].u_csrng_cmd_stage
    `define CMD_STAGE_2 tb.dut.u_csrng_core.gen_cmd_stage[2].u_csrng_cmd_stage

    `define HIER_PATH(prefix, suffix) `"prefix.suffix`"

    // Turn off assertions
    $assertoff(0, "tb.entropy_src_if.ReqHighUntilAck_A");
    $assertoff(0, "tb.entropy_src_if.AckAssertedOnlyWhenReqAsserted_A");
    $assertoff(0, "tb.dut.u_csrng_core.u_prim_arbiter_ppc_updblk_arb.LockArbDecision_A");
    $assertoff(0, "tb.dut.u_csrng_core.u_prim_arbiter_ppc_benblk_arb.ReqStaysHighUntilGranted0_M");
    $assertoff(0, "tb.dut.u_csrng_core.u_prim_arbiter_ppc_updblk_arb.ReqStaysHighUntilGranted0_M");
    $assertoff(0, `HIER_PATH(`CMD_STAGE_0, u_state_regs_A));
    $assertoff(0, `HIER_PATH(`CMD_STAGE_1, u_state_regs_A));
    $assertoff(0, `HIER_PATH(`CMD_STAGE_2, u_state_regs_A));
    $assertoff(0, `HIER_PATH(`CMD_STAGE_0, CsrngCmdStageGenbitsFifoPushExpected_A));
    $assertoff(0, `HIER_PATH(`CMD_STAGE_1, CsrngCmdStageGenbitsFifoPushExpected_A));
    $assertoff(0, `HIER_PATH(`CMD_STAGE_2, CsrngCmdStageGenbitsFifoPushExpected_A));
    cfg.csrng_assert_vif.assert_off();
    `DV_ASSERT_CTRL_REQ("CmdStageFifoAsserts", 0)

    cs_item = csrng_item::type_id::create("cs_item");

    // Write CSRNG Cmd_Req - Instantiate Command
    cs_item.acmd  = csrng_pkg::INS;
    cs_item.clen  = 'h0;
    cs_item.flags = MuBi4True;
    cs_item.glen  = 'h0;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(cfg.which_app_err_alert, cs_item);

    // Write CSRNG Cmd_Req Register - Generate Command
    cs_item.acmd  = csrng_pkg::GEN;
    cs_item.clen  = 'h0;
    cs_item.flags = MuBi4True;
    cs_item.glen  = 'h1000;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    // Not waiting for response so the error happens in the middle of the generate command.
    send_cmd_req(cfg.which_app_err_alert, cs_item, .await_response(1'b0));

    reg_name = "err_code";
    csr = ral.get_reg_by_name(reg_name);
    fld_name = cfg.which_err_code.name();

    first_index = find_index("_", fld_name, "first");
    last_index = find_index("_", fld_name, "last");

    `uvm_info(`gfn, $sformatf("While app %d handles a generate command, we will insert error %s",
                              cfg.which_app_err_alert, fld_name), UVM_MEDIUM)

    case (cfg.which_err_code) inside
      sfifo_cmd_err, sfifo_genbits_err, sfifo_cmdreq_err, sfifo_rcstage_err, sfifo_keyvrc_err,
      sfifo_bencreq_err, sfifo_final_err, sfifo_gbencack_err, sfifo_grcstage_err,
      sfifo_gadstage_err, sfifo_ggenbits_err, sfifo_blkenc_err, sfifo_updreq_err,
      sfifo_bencack_err, sfifo_pdata_err, sfifo_ggenreq_err: begin
        fld = csr.get_field_by_name(fld_name);
        fifo_base_path = fld_name.substr(0, last_index-1);

        foreach (path_exts[i]) begin
          fifo_forced_paths[i] = cfg.csrng_path_vif.fifo_err_path(cfg.which_app_err_alert,
                                                                  fifo_base_path, path_exts[i]);
        end

        `uvm_info(`gfn, $sformatf("Forcing this FIFO error type %s", cfg.which_fifo_err.name()),
                  UVM_MEDIUM)

        if (cfg.which_err_code == sfifo_updreq_err || cfg.which_err_code == sfifo_bencack_err ||
            cfg.which_err_code == sfifo_pdata_err || cfg.which_err_code == sfifo_ggenreq_err) begin
          force_all_fifo_errs_exception(fifo_forced_paths, fifo_forced_values, path_exts, fld,
                                        1'b1, cfg.which_fifo_err);
        end else begin
          force_all_fifo_errs(fifo_forced_paths, fifo_forced_values, path_exts, fld,
                              1'b1, cfg.which_fifo_err);
        end
        csr_rd(.ptr(ral.err_code), .value(backdoor_err_code_val));
        cov_vif.cg_err_code_sample(.err_code(backdoor_err_code_val));
      end
      cmd_stage_sm_err, main_sm_err, drbg_gen_sm_err, drbg_updbe_sm_err, drbg_updob_sm_err: begin
        fld = csr.get_field_by_name(fld_name);
        path = cfg.csrng_path_vif.sm_err_path(fld_name.substr(0, last_index-1),
                                              cfg.which_app_err_alert);
        force_path_err(path, 8'b0, fld, 1'b1);
        csr_rd(.ptr(ral.err_code), .value(backdoor_err_code_val));
        cov_vif.cg_err_code_sample(.err_code(backdoor_err_code_val));
      end
      aes_cipher_sm_err: begin
        // Get the path to the AES cipher core FSM. We need it in any case to test that AES enters
        // the terminal error state.
        string aes_fsm_path;
        logic [aes_pkg::CipherCtrlStateWidth-1:0] aes_fsm_state;
        if (aes_pkg::SP2V_LOGIC_HIGH[cfg.which_sp2v] == 1'b1) begin
          aes_fsm_path = cfg.csrng_path_vif.aes_cipher_fsm_err_path(cfg.which_sp2v, "p");
        end else begin
          aes_fsm_path = cfg.csrng_path_vif.aes_cipher_fsm_err_path(cfg.which_sp2v, "n");
        end
        fld = csr.get_field_by_name(fld_name);
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
            force_path_err(aes_fsm_path, value3, fld, 1'b1);
          end
          ctrl_sparse: begin
            // We force one rail of one of the mux control signals to another valid encoding.
            value3 = {3'b000, {aes_pkg::ADD_RK_INIT}};
            if (aes_pkg::SP2V_LOGIC_HIGH[cfg.which_sp2v] == 1'b1) begin
              path = cfg.csrng_path_vif.aes_cipher_ctrl_err_path(cfg.which_sp2v, "p");
              force_path_err(path, value3, fld, 1'b1);
            end else begin
              path = cfg.csrng_path_vif.aes_cipher_ctrl_err_path(cfg.which_sp2v, "n");
              force_path_err(path, value3, fld, 1'b1);
            end
          end
          ctr_redun: begin
            value4 = 4'hf;
            if (aes_pkg::SP2V_LOGIC_HIGH[cfg.which_sp2v] == 1'b1) begin
              path = cfg.csrng_path_vif.aes_cipher_rnd_ctr_err_path(cfg.which_sp2v, "p");
              force_path_err(path, value4, fld, 1'b1);
            end else begin
              path = cfg.csrng_path_vif.aes_cipher_rnd_ctr_err_path(cfg.which_sp2v, "n");
              force_path_err(path, value4, fld, 1'b1);
            end
          end
        endcase
        csr_rd(.ptr(ral.err_code), .value(backdoor_err_code_val));
        cov_vif.cg_err_code_sample(.err_code(backdoor_err_code_val));
        // Check that the AES cipher core FSM has entered the terminal error state.
        `DV_CHECK(uvm_hdl_read(aes_fsm_path, aes_fsm_state))
        `DV_CHECK_EQ(aes_fsm_state, aes_pkg::CIPHER_CTRL_ERROR)
      end
      cmd_gen_cnt_err: begin
        logic [csrng_pkg::MainSmStateWidth-1:0] sm_state;
        string sm_state_path = cfg.csrng_path_vif.sm_err_path("main_sm", cfg.which_app_err_alert);
        case(cfg.which_cnt) inside
          cmd_gen_cnt_sel: begin
            fld = csr.get_field_by_name(fld_name);
            path = cfg.csrng_path_vif.cmd_gen_cnt_err_path(cfg.which_app_err_alert);
            force_cnt_err(path, fld, 1'b1, 13);
          end
          drbg_upd_cnt_sel: begin
            fld = csr.get_field_by_name(fld_name);
            path = cfg.csrng_path_vif.drbg_upd_cnt_err_path();
            force_cnt_err(path, fld, 1'b1, 32);
          end
          drbg_gen_cnt_sel: begin
            fld = csr.get_field_by_name(fld_name);
            path = cfg.csrng_path_vif.drbg_gen_cnt_err_path();
            force_cnt_err(path, fld, 1'b1, 32);
          end
        endcase
        csr_rd(.ptr(ral.err_code), .value(backdoor_err_code_val));
        cov_vif.cg_err_code_sample(.err_code(backdoor_err_code_val));
        // Check that the `csrng_main_sm` FSM, which observes the errors of the faulted counter, has
        // entered the error state.
        `DV_CHECK(uvm_hdl_read(sm_state_path, sm_state))
        `DV_CHECK_EQ(sm_state, csrng_pkg::MainSmError)
      end
      fifo_write_err, fifo_read_err, fifo_state_err: begin
        fld = csr.get_field_by_name(fld_name);
        fifo_name = cfg.which_fifo.name();
        `uvm_info(`gfn, $sformatf("Injecting fault in %s", fifo_name), UVM_MEDIUM)
        path_key = fld_name.substr(first_index+1, last_index-1);

        path1 = cfg.csrng_path_vif.fifo_err_path(cfg.which_app_err_alert, fifo_name,
                                                 fifo_err_path[0][path_key]);
        path2 = cfg.csrng_path_vif.fifo_err_path(cfg.which_app_err_alert, fifo_name,
                                                 fifo_err_path[1][path_key]);
        if (cfg.which_err_code == fifo_write_err) begin
          path3 = cfg.csrng_path_vif.fifo_err_path(cfg.which_app_err_alert, fifo_name,
                                                   "wdata");
        end else if (cfg.which_err_code == fifo_read_err) begin
          path3 = cfg.csrng_path_vif.fifo_err_path(cfg.which_app_err_alert, fifo_name,
                                                   "rdata");
        end

        value1 = fifo_err_value[0][path_key];
        value2 = fifo_err_value[1][path_key];

        if (cfg.which_err_code == fifo_read_error &&
           ((cfg.which_fifo == sfifo_ggenreq) || (cfg.which_fifo == sfifo_pdata) ||
            (cfg.which_fifo == sfifo_bencack) || (cfg.which_fifo == sfifo_updreq)))
        begin
          force_fifo_err_exception(path1, path2, 1'b1, 1'b0, 1'b0, fld, 1'b1);
        end else if (cfg.which_err_code == fifo_write_error ||
                     cfg.which_err_code == fifo_read_err) begin
          force_fifo_readwrite_err(path1, path2, path3, value1, value2, 8'b0, fld, 1'b1);
        end else begin
          force_fifo_err(path1, path2, value1, value2, fld, 1'b1);
        end
        csr_rd(.ptr(ral.err_code), .value(backdoor_err_code_val));
        cov_vif.cg_err_code_sample(.err_code(backdoor_err_code_val));
      end
      sfifo_cmd_err_test, sfifo_genbits_err_test, sfifo_cmdreq_err_test, sfifo_rcstage_err_test,
      sfifo_keyvrc_err_test, sfifo_updreq_err_test, sfifo_bencreq_err_test, sfifo_bencack_err_test,
      sfifo_pdata_err_test, sfifo_final_err_test, sfifo_gbencack_err_test, sfifo_grcstage_err_test,
      sfifo_ggenreq_err_test, sfifo_gadstage_err_test, sfifo_ggenbits_err_test,
      sfifo_blkenc_err_test, cmd_stage_sm_err_test, main_sm_err_test, drbg_gen_sm_err_test,
      drbg_updbe_sm_err_test, drbg_updob_sm_err_test, aes_cipher_sm_err_test, cmd_gen_cnt_err_test,
      fifo_write_err_test, fifo_read_err_test, fifo_state_err_test: begin
        fld = csr.get_field_by_name(fld_name.substr(0, last_index-1));
        err_code_test_bit = fld.get_lsb_pos();
        csr_wr(.ptr(ral.err_code_test.err_code_test), .value(err_code_test_bit));
        cfg.clk_rst_vif.wait_clks(50);
        csr_rd_check(.ptr(fld), .compare_value(1'b1));
        // Since we already did a backdoor check, sampling with this value is sufficient.
        cov_vif.cg_err_test_sample(.err_test_code(err_code_test_bit));
        // Clear interrupt_enable
        csr_wr(.ptr(ral.intr_enable), .value(32'd0));
        ral.ctrl.enable.set(prim_mubi_pkg::MuBi4False);
        ral.ctrl.sw_app_enable.set(prim_mubi_pkg::MuBi4True);
        csr_update(.csr(ral.ctrl));
        // Expect/Clear interrupt bit
        check_interrupts(.interrupts((1 << FifoErr)), .check_set(1'b1));
      end
      default: begin
        `uvm_fatal(`gfn, "Invalid case! (bug in environment)")
      end
    endcase // case (cfg.which_err_code)

    cfg.clk_rst_vif.wait_clks(50);
    // Clear intr_enable
    csr_wr(.ptr(ral.intr_enable), .value(32'h0));
    ral.ctrl.enable.set(prim_mubi_pkg::MuBi4False);
    csr_update(.csr(ral.ctrl));
    // Clear intr_state
    csr_wr(.ptr(ral.intr_state), .value(32'd15));
    cfg.clk_rst_vif.wait_clks(100);

    if (cfg.which_err_code inside {cmd_stage_sm_err, cmd_stage_sm_err_test,
                                   main_sm_err, main_sm_err_test,
                                   drbg_gen_sm_err, drbg_gen_sm_err_test,
                                   drbg_updbe_sm_err, drbg_updbe_sm_err_test,
                                   drbg_updob_sm_err, drbg_updob_sm_err_test,
                                   aes_cipher_sm_err, aes_cipher_sm_err_test,
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
    $asserton(0, `HIER_PATH(`CMD_STAGE_0, u_state_regs_A));
    $asserton(0, `HIER_PATH(`CMD_STAGE_1, u_state_regs_A));
    $asserton(0, `HIER_PATH(`CMD_STAGE_2, u_state_regs_A));
    $asserton(0, `HIER_PATH(`CMD_STAGE_0, CsrngCmdStageGenbitsFifoPushExpected_A));
    $asserton(0, `HIER_PATH(`CMD_STAGE_1, CsrngCmdStageGenbitsFifoPushExpected_A));
    $asserton(0, `HIER_PATH(`CMD_STAGE_2, CsrngCmdStageGenbitsFifoPushExpected_A));

    `undef CMD_STAGE_0
    `undef CMD_STAGE_1
    `undef CMD_STAGE_2

    `undef HIER_PATH

    cfg.csrng_assert_vif.assert_on();

  endtask : body

endclass : csrng_err_vseq
