// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test ERR_CODE fields fired as expected, as well as ERR_CODE_TEST register

class csrng_err_vseq extends csrng_base_vseq;
  `uvm_object_utils(csrng_err_vseq)

  `uvm_object_new

  csrng_item   cs_item;

  task body();
    bit [2:0]     SP2V_LOGIC_HIGH = '{1'b0,1'b1,1'b1};
    bit [5:0]     err_code_test_bit;
    string        path, path1, path2;
    bit           value1, value2;
    string        fifo_name;
    int           first_index, last_index;
    string        fifo_base_path;
    string        path_exts [4] = {"push", "full", "pop", "not_empty"};
    string        fifo_forced_paths [4];
    bit           fifo_forced_values [4] = {1'b1, 1'b1, 1'b1, 1'b0};
    string        fifo_err_path [2][string];
    bit           fifo_err_value [2][string];
    string        path_key;
    string        reg_name, fld_name;
    uvm_reg       csr;
    uvm_reg_field fld;

    fifo_err_path[0] = '{"write": "push", "read": "pop", "state": "full"};
    fifo_err_path[1] = '{"write": "full", "read": "not_empty", "state": "not_empty"};
    fifo_err_value[0] = '{"write": 1'b1, "read": 1'b1, "state": 1'b1};
    fifo_err_value[1] = '{"write": 1'b1, "read": 1'b0, "state": 1'b0};

    // Turn off fatal alert check
    expect_fatal_alerts = 1'b1;

    // Turn off assertions
    $assertoff(0, "tb.entropy_src_if.ReqHighUntilAck_A");
    $assertoff(0, "tb.entropy_src_if.AckAssertedOnlyWhenReqAsserted_A");
    $assertoff(0, "tb.dut.u_csrng_core.u_prim_arbiter_ppc_updblk_arb.LockArbDecision_A");
    $assertoff(0, "tb.dut.u_csrng_core.u_prim_arbiter_ppc_benblk_arb.ReqStaysHighUntilGranted0_M");
    $assertoff(0, "tb.dut.u_csrng_core.u_prim_arbiter_ppc_updblk_arb.ReqStaysHighUntilGranted0_M");
    cfg.csrng_assert_vif.assert_off();

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

    reg_name = "err_code";
    csr = ral.get_reg_by_name(reg_name);
    fld_name = cfg.which_err_code.name();

    first_index = find_index("_", fld_name, "first");
    last_index = find_index("_", fld_name, "last");

    case (cfg.which_err_code) inside
      sfifo_cmd_err, sfifo_genbits_err, sfifo_cmdreq_err, sfifo_rcstage_err, sfifo_keyvrc_err,
      sfifo_bencreq_err, sfifo_final_err, sfifo_gbencack_err, sfifo_grcstage_err,
      sfifo_gadstage_err, sfifo_ggenbits_err, sfifo_blkenc_err, sfifo_updreq_err,
      sfifo_bencack_err, sfifo_pdata_err, sfifo_ggenreq_err: begin
        fld = csr.get_field_by_name(fld_name);
        fifo_base_path = fld_name.substr(0, last_index-1);

        foreach (path_exts[i]) begin
          fifo_forced_paths[i] = cfg.csrng_path_vif.fifo_err_path(cfg.NHwApps, fifo_base_path,
                                                                  path_exts[i]);
        end

        if (cfg.which_err_code == sfifo_updreq_err || cfg.which_err_code == sfifo_bencack_err ||
            cfg.which_err_code == sfifo_pdata_err || cfg.which_err_code == sfifo_ggenreq_err) begin
          force_all_fifo_errs_exception(fifo_forced_paths, fifo_forced_values, path_exts, fld,
                                        1'b1, cfg.which_fifo_err);
        end else begin
          force_all_fifo_errs(fifo_forced_paths, fifo_forced_values, path_exts, fld,
                              1'b1, cfg.which_fifo_err);
        end
      end
      cmd_stage_sm_err, main_sm_err, drbg_gen_sm_err, drbg_updbe_sm_err, drbg_updob_sm_err: begin
        fld = csr.get_field_by_name(fld_name);
        path = cfg.csrng_path_vif.sm_err_path(fld_name.substr(0, last_index-1), cfg.NHwApps);
        force_path_err(path, 8'b0, fld, 1'b1);
      end
      aes_cipher_sm_err: begin
        fld = csr.get_field_by_name(fld_name);
        if (SP2V_LOGIC_HIGH[cfg.which_sp2v] == 1'b1) begin
          path = cfg.csrng_path_vif.aes_cipher_sm_err_path(cfg.which_sp2v, "p");
          force_path_err(path, 8'b0, fld, 1'b1);
        end else begin
          path = cfg.csrng_path_vif.aes_cipher_sm_err_path(cfg.which_sp2v, "n");
          force_path_err(path, 8'b0, fld, 1'b1);
        end
      end
      cmd_gen_cnt_err: begin
        fld = csr.get_field_by_name(fld_name);
        path = cfg.csrng_path_vif.cmd_gen_cnt_err_path(cfg.NHwApps);
        force_path_err(path, 8'h01, fld, 1'b1);
      end
      fifo_write_err, fifo_read_err, fifo_state_err: begin
        fld = csr.get_field_by_name(fld_name);
        fifo_name = cfg.which_fifo.name();
        path_key = fld_name.substr(first_index+1, last_index-1);

        path1 = cfg.csrng_path_vif.fifo_err_path(cfg.NHwApps, fifo_name,
                                                 fifo_err_path[0][path_key]);
        path2 = cfg.csrng_path_vif.fifo_err_path(cfg.NHwApps, fifo_name,
                                                 fifo_err_path[1][path_key]);
        value1 = fifo_err_value[0][path_key];
        value2 = fifo_err_value[1][path_key];

        if (cfg.which_err_code == fifo_read_error &&
           ((cfg.which_fifo == sfifo_ggenreq) || (cfg.which_fifo == sfifo_pdata) ||
            (cfg.which_fifo == sfifo_bencack) || (cfg.which_fifo == sfifo_updreq)))
        begin
          force_fifo_err_exception(path1, path2, 1'b1, 1'b0, 1'b0, fld, 1'b1);
        end else begin
          force_fifo_err(path1, path2, value1, value2, fld, 1'b1);
        end
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
    csr_rd_check(.ptr(ral.intr_state), .compare_value(4'b0));

    // Turn assertions back on
    $asserton(0, "tb.entropy_src_if.ReqHighUntilAck_A");
    $asserton(0, "tb.entropy_src_if.AckAssertedOnlyWhenReqAsserted_A");
    $asserton(0, "tb.dut.u_csrng_core.u_prim_arbiter_ppc_updblk_arb.LockArbDecision_A");
    $asserton(0, "tb.dut.u_csrng_core.u_prim_arbiter_ppc_benblk_arb.ReqStaysHighUntilGranted0_M");
    $asserton(0, "tb.dut.u_csrng_core.u_prim_arbiter_ppc_updblk_arb.ReqStaysHighUntilGranted0_M");
    cfg.csrng_assert_vif.assert_on();

  endtask : body

endclass : csrng_err_vseq
