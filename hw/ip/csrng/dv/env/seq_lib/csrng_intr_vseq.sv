// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test cs_cmd_req_done, cs_entropy_req, cs_hw_inst_exc and cs_fatal_err interrupts
// fired as expected

class csrng_intr_vseq extends csrng_base_vseq;
  `uvm_object_utils(csrng_intr_vseq)

  `uvm_object_new

  csrng_item   cs_item;
  string       path1, path2, path_push, path_full, path_pop, path_not_empty, path;
  int          Sp2VWidth = 3;
  bit [2:0]    SP2V_LOGIC_HIGH = '{1'b0,1'b1,1'b1};

  task test_cs_cmd_req_done();
    cs_item = csrng_item::type_id::create("cs_item");

    // Write CSRNG Cmd_Req - Instantiate Command
    cs_item.acmd  = csrng_pkg::INS;
    cs_item.clen  = 'h0;
    cs_item.flags = 'h1;
    cs_item.glen  = 'h0;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(SW_APP, cs_item);

    // Write CSRNG Cmd_Req Register - Generate Command
    cs_item.acmd  = csrng_pkg::GEN;
    cs_item.clen  = 'h0;
    cs_item.flags = 'h1;
    cs_item.glen  = 'h1;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(SW_APP, cs_item);
  endtask // test_cs_cmd_req_done

  task test_cs_entropy_req();
    cs_item = csrng_item::type_id::create("cs_item");

    // Write CSRNG Cmd_Req - Instantiate Command
    cs_item.acmd  = csrng_pkg::INS;
    cs_item.clen  = 'h0;
    cs_item.flags = 'h0;
    cs_item.glen  = 'h0;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(SW_APP, cs_item);

    // Write CSRNG Cmd_Req Register - Generate Command
    cs_item.acmd  = csrng_pkg::GEN;
    cs_item.clen  = 'h0;
    cs_item.flags = 'h0;
    cs_item.glen  = 'h1;
    `uvm_info(`gfn, $sformatf("%s", cs_item.convert2string()), UVM_DEBUG)
    send_cmd_req(SW_APP, cs_item);

    // Expect/Clear interrupt bit
    csr_rd_check(.ptr(ral.intr_state.cs_entropy_req), .compare_value(1'b1));
    check_interrupts(.interrupts((1 << EntropyReq)), .check_set(1'b1));
    cfg.clk_rst_vif.wait_clks(100);
    // Make sure the interrupt bit is cleared
    csr_rd_check(.ptr(ral.intr_state.cs_entropy_req), .compare_value(1'b0));
  endtask // test_cs_entropy_req

  task test_cs_hw_inst_exc();
    path1 = cfg.csrng_path_vif.cs_hw_inst_exc_path("ack", cfg.which_hw_inst_exc);
    path2 = cfg.csrng_path_vif.cs_hw_inst_exc_path("ack_sts", cfg.which_hw_inst_exc);

    force_path(path1, path2, 1'b1, 1'b0);
    // Wait for cs_hw_inst_exc interrupt
    csr_spinwait(.ptr(ral.intr_state.cs_hw_inst_exc), .exp_data(1'b1));

    `DV_CHECK(uvm_hdl_release(path1));
    `DV_CHECK(uvm_hdl_release(path2));

    // Expect/Clear interrupt bit
    check_interrupts(.interrupts((1 << HwInstExc)), .check_set(1'b1));
    cfg.clk_rst_vif.wait_clks(100);
    // Make sure the interrupt bit is cleared
    csr_rd_check(.ptr(ral.intr_state.cs_hw_inst_exc), .compare_value(1'b0));
  endtask // test_cs_hw_inst_exc

  task test_cs_fatal_err();
    string        path, path1, path2;
    bit           value1, value2;
    string        fifo_name, fld_name;
    int           first_index, last_index;
    string        fifo_base_path;
    string        path_exts [4] = {"push", "full", "pop", "not_empty"};
    string        fifo_forced_paths [4];
    bit           fifo_forced_values [4] = {1'b1, 1'b1, 1'b1, 1'b0};
    string        fifo_err_path [2][string];
    bit           fifo_err_value [2][string];
    string        path_key;

    fifo_err_path[0] = '{"write": "push", "read": "pop", "state": "full"};
    fifo_err_path[1] = '{"write": "full", "read": "not_empty", "state": "not_empty"};
    fifo_err_value[0] = '{"write": 1'b1, "read": 1'b1, "state": 1'b1};
    fifo_err_value[1] = '{"write": 1'b1, "read": 1'b0, "state": 1'b0};

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
        if (SP2V_LOGIC_HIGH[cfg.which_sp2v] == 1'b1) begin
          path = cfg.csrng_path_vif.aes_cipher_sm_err_path(cfg.which_sp2v, "p");
          force_path_err(path, 8'b0, ral.intr_state.cs_fatal_err, 1'b1);
        end else begin
          path = cfg.csrng_path_vif.aes_cipher_sm_err_path(cfg.which_sp2v, "n");
          force_path_err(path, 8'b0, ral.intr_state.cs_fatal_err, 1'b1);
        end
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
  endtask // test_cs_fatal_err

  task body();
    // Turn off fatal alert check
    expect_fatal_alerts = 1'b1;

    // Turn off assertions
    $assertoff(0, "tb.entropy_src_if.ReqHighUntilAck_A");
    $assertoff(0, "tb.entropy_src_if.AckAssertedOnlyWhenReqAsserted_A");
    $assertoff(0, "tb.dut.u_csrng_core.u_prim_arbiter_ppc_updblk_arb.LockArbDecision_A");
    $assertoff(0, "tb.dut.u_csrng_core.u_csrng_ctr_drbg_upd.u_prim_count_ctr_drbg.SimulClrSet_A");
    $assertoff(0, "tb.dut.u_csrng_core.u_prim_arbiter_ppc_benblk_arb.ReqStaysHighUntilGranted0_M");
    $assertoff(0, "tb.dut.u_csrng_core.u_prim_arbiter_ppc_updblk_arb.ReqStaysHighUntilGranted0_M");
    cfg.csrng_assert_vif.assert_off();

    // Test cs_cmd_req_done interrupt
    // cs_cmd_req_done interrupt is checked in the send_cmd_req()
    test_cs_cmd_req_done();

    // Test cs_entropy_req interrupt
    test_cs_entropy_req();

    // Test cs_hw_inst_exc interrupt
    test_cs_hw_inst_exc();

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
    csr_rd_check(.ptr(ral.intr_state), .compare_value(4'b0));

    // Turn assertions back on
    $asserton(0, "tb.entropy_src_if.ReqHighUntilAck_A");
    $asserton(0, "tb.entropy_src_if.AckAssertedOnlyWhenReqAsserted_A");
    $asserton(0, "tb.dut.u_csrng_core.u_prim_arbiter_ppc_updblk_arb.LockArbDecision_A");
    $asserton(0, "tb.dut.u_csrng_core.u_csrng_ctr_drbg_upd.u_prim_count_ctr_drbg.SimulClrSet_A");
    $asserton(0, "tb.dut.u_csrng_core.u_prim_arbiter_ppc_benblk_arb.ReqStaysHighUntilGranted0_M");
    $asserton(0, "tb.dut.u_csrng_core.u_prim_arbiter_ppc_updblk_arb.ReqStaysHighUntilGranted0_M");
    cfg.csrng_assert_vif.assert_on();

  endtask : body

endclass : csrng_intr_vseq
