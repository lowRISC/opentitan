// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Otp_ctrl_init_fail_vseq is developed to check if otp_ctrl reacts correctly if initialization
// failed.
// Note that scoreboard is disabled in this test and all checks are done within this sequence.
// This test writes and reads to OTP_memory via DAI interface, then triggers digest calculations.
// Afterwards instead of issuing reset, this sequence continues to write to DAI interface.
// If any of the hardware partition is updated, then in next power cycle, the initialization will
// fail.
// If no check failure, we will random inject ECC errors to create init macro errors.
// We will also trigger sw partition ECC reg failure by forcing the ECC reg error output.
//
// This sequence will check the following items if OTP init failed with fatal error:
// - Otp_initialization failure triggers fatal alert
// - Status register reflect the correct error
// - Otp_ctrl's power init output stays 0
// This sequence will check the following items if OTP init failed with correctable error:
// - Otp_initialtion passed with power init output changes to 1
// - Otp status and interrupt reflect the correct error message

class otp_ctrl_init_fail_vseq extends otp_ctrl_smoke_vseq;
  `uvm_object_utils(otp_ctrl_init_fail_vseq)

  `uvm_object_new

  rand uint         num_to_lock_digests;
  bit [NumPart-1:0] init_chk_err;
  bit               part_locked;

  // If num_to_lock_digests is larger than num_dai_op, that means there won't be OTP init check
  // error, so this sequence will trigger ECC error instead.
  // We set 25% possibility that OTP init check fails due to writing OTP after digest is locked.
  constraint lock_digest_c {num_to_lock_digests < num_dai_op * 4;}
  constraint num_iterations_c {num_dai_op inside {[20:100]};}
  constraint ecc_otp_err_c {
    $countones(ecc_otp_err) dist {OtpNoEccErr     :/ 2,
                                  OtpEccCorrErr   :/ 2,
                                  OtpEccUncorrErr :/ 1};
  }

  virtual task pre_start();
    super.pre_start();
    num_to_lock_digests.rand_mode(0);
  endtask

  task body();
    bit [TL_DW-1:0] exp_status;
    `uvm_info(`gfn, $sformatf("Number of dai operation is %0d, number to lock digest is %0d",
              num_dai_op, num_to_lock_digests), UVM_MEDIUM)

    for (uint i = 0; i <= num_dai_op; i++) begin
      bit [TL_DW-1:0] tlul_val;
      if (cfg.stop_transaction_generators()) return;

      `DV_CHECK_RANDOMIZE_FATAL(this)
      `uvm_info(`gfn, $sformatf("starting dai access seq %0d/%0d with addr %0h in partition %0d",
                i, num_dai_op, dai_addr, part_idx), UVM_MEDIUM)

      if (i > num_to_lock_digests && PartInfo[part_idx].hw_digest &&
          !used_dai_addrs.exists(dai_addr)) begin
        init_chk_err[part_idx] = 1;
      end

      // OTP write via DAI
      dai_wr(dai_addr, wdata0, wdata1);

      // OTP read via DAI, check data in scb
      dai_rd(dai_addr, wdata0, wdata1);

      // If write sw partitions, check tlul window
      if (is_sw_part(dai_addr)) begin
        uvm_reg_addr_t tlul_addr = cfg.ral.get_addr_from_offset(get_sw_window_offset(dai_addr));
        tl_access(.addr(tlul_addr), .write(0), .data(tlul_val), .blocking(1), .check_rsp(0));
      end

      if (i == num_to_lock_digests) begin
        cal_hw_digests('1);
        part_locked = 1;
      end

      csr_rd(ral.status, tlul_val);
    end

    do_otp_ctrl_init = 0;
    do_otp_pwr_init  = 0;
    cfg.en_scb       = 0;
    dut_init();

    if (init_chk_err) begin
      `uvm_info(`gfn, $sformatf("OTP_init check failure with init error = %0h", init_chk_err),
                UVM_LOW)
      foreach(init_chk_err[i]) begin
  if (cfg.stop_transaction_generators()) break;
        if (init_chk_err[i]) exp_status |= 1'b1 << i;
      end

      check_otp_fatal_err("fatal_check_error", exp_status);

    // If not check error, force ECC correctable and uncorrectable error
    end else begin
      bit             is_fatal, is_correctable;
      bit [TL_DW-1:0] addr;

      for (int i = 0; i < NumPart; i++) begin
        if (cfg.stop_transaction_generators()) return;
        `DV_CHECK_RANDOMIZE_FATAL(this);

        if (PartInfo[i].sw_digest) begin
          // During OTP init, SW partitions only read digest value
          addr = PART_OTP_DIGEST_ADDRS[i] << 2;
        end else begin
          // During OTP init, non SW partitions read all value
          addr = $urandom_range(PartInfo[i].offset, PartInfo[i].offset + PartInfo[i].size - 1);
        end

        void'(backdoor_inject_ecc_err(addr, ecc_otp_err));
        // VendorTest partition's ECC error is not fatal.
        if (!is_fatal && ecc_otp_err == OtpEccUncorrErr && part_has_integrity(i)) begin
          is_fatal = 1;
        end else if (!is_correctable && ecc_otp_err == OtpEccCorrErr && part_has_integrity(i)) begin
          is_correctable = 1;
        end
        if (ecc_otp_err != OtpNoEccErr && part_has_integrity(i)) exp_status[i] = 1;
      end

      if (is_fatal) begin
        // ECC uncorrectable error.
        `uvm_info(`gfn, "OTP_init macro ECC uncorrectable failure", UVM_LOW)
        check_otp_fatal_err("fatal_macro_error", exp_status);
      end else if ($urandom_range(0, 1)) begin

        // Randomly force ECC reg in sw partitions to create a check failure.
        // Totaly three sw partitions, and each bit indexes a partition.
        bit [NumPartUnbuf-1:0] sw_check_fail = $urandom_range(1, (1'b1<<NumPartUnbuf)-1);
        cfg.otp_ctrl_vif.force_sw_check_fail(sw_check_fail);
        `uvm_info(`gfn, $sformatf("OTP_init SW ECC check failure with index %0h", sw_check_fail),
                  UVM_LOW)
        foreach(sw_check_fail[i]) begin
          if (sw_check_fail[i]) exp_status[i] = 1;
        end
        check_otp_fatal_err("fatal_check_error", exp_status);
      end else begin

        // Expect the OTP init to continue with an ECC correctable interrupt.
        `uvm_info(`gfn, "OTP_init macro ECC correctable failure", UVM_LOW)
        exp_status[OtpDaiIdleIdx] = 1;
        cfg.otp_ctrl_vif.drive_pwr_otp_init(1);
        wait(cfg.otp_ctrl_vif.pwr_otp_done_o == 1);
        wait(cfg.otp_ctrl_vif.pwr_otp_idle_o == 1);
        csr_rd_check(.ptr(ral.status), .compare_value(exp_status));
        if (is_correctable) csr_rd_check(.ptr(ral.intr_state.otp_error), .compare_value(1));

        // Clear backdoor injected errors.
        cfg.mem_bkdr_util_h.clear_mem();
        exp_status[OtpDaiIdleIdx] = 0;

        if (part_locked) begin
          // Digest check failure because the memory is cleared.
          // Since OtpHwCfg0 is the first partition with HW digest, this partition's check error
          // will be triggered first.
          `uvm_info(`gfn, "OTP digest check failure", UVM_LOW)
          exp_status[OtpHwCfg0ErrIdx] = 1;
        end else begin
          // Create LC check failure.
          `uvm_info(`gfn, "OTP_init LC failure", UVM_LOW)
          cfg.otp_ctrl_vif.lc_check_byp_en = 0;
          req_lc_transition(1);
          exp_status[OtpLifeCycleErrIdx] = 1;
        end
        trigger_checks(.val('1), .wait_done(0));
        check_otp_fatal_err("fatal_check_error", exp_status);
      end
    end
  endtask

  virtual task check_otp_fatal_err(string alert_name, bit [TL_DW-1:0] exp_status);
    int            error_cnt;
    otp_err_code_e exp_err_code = (alert_name == "fatal_check_error") ?
                                  OtpCheckFailError : OtpMacroEccUncorrError;
    uvm_reg_data_t err_code_raw;
    otp_err_code_e err_code;
    dv_base_reg_field err_code_flds[$];

    cfg.otp_ctrl_vif.drive_pwr_otp_init(1);

    // Wait until OTP_INIT process the error
    `DV_SPINWAIT_EXIT(wait(cfg.m_alert_agent_cfgs[alert_name].vif.alert_tx_final.alert_p);,
                      cfg.clk_rst_vif.wait_clks(5000);,
                      $sformatf("Timeout waiting for alert %0s", alert_name))
    check_fatal_alert_nonblocking(alert_name);

    // If fatal_macro_error, will trigger fatal_check_error alert due to internal escalation.
    if (alert_name == "fatal_macro_error") check_fatal_alert_nonblocking("fatal_check_error");

    cfg.otp_ctrl_vif.drive_pwr_otp_init(0);

    // Wait until all partitions finish initialization
    cfg.clk_rst_vif.wait_clks($urandom_range(2000, 4000));

    // Here we should see alert is triggered by one of the fatal errors, then it triggers internal
    // escalation. The logic below tries to confirm the first fatal alert is triggered with the
    // correct error code.
    for (int i = 0; i <= OtpLciErrIdx; i++) begin
      ral.err_code[i].get_dv_base_reg_fields(err_code_flds);
      if (exp_status[i]) begin
        csr_rd(err_code_flds[0], err_code_raw);
        err_code = otp_err_code_e'(err_code_raw);
        if (err_code == exp_err_code) begin
          error_cnt++;
        end else if (err_code != OtpFsmStateError) begin
          `uvm_error(`gfn, $sformatf("Unexpected error code_%0d: %0s", i, err_code.name))
        end
        if (cfg.en_cov) cov.collect_err_code_cov(i, err_code);
      end
    end

    // More than one fatal alert causes could be triggered at the same time
    `DV_CHECK_GT(error_cnt, 0)
    csr_rd_check(.ptr(ral.status), .compare_value(exp_status | FATAL_EXP_STATUS));

    `DV_CHECK_EQ(cfg.otp_ctrl_vif.pwr_otp_done_o, 1)
    `DV_CHECK_EQ(cfg.otp_ctrl_vif.pwr_otp_idle_o, 1)

    // Issue reset to stop fatal alert
    cfg.otp_ctrl_vif.release_sw_check_fail();
    apply_reset();

    // delay to avoid race condition when sending item and checking no item after reset occur
    // at the same time
    #1ps;
  endtask

endclass
