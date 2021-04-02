// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Otp_ctrl_init_fail_vseq is developed to check if OTP_CTRL reacts correctly if initialization
// failed.
// Note that coreboard is disabled in this test and all checks are done within sequence.
// This test writes and reads to OTP_memory via DAI interface, then triggers digest calculations.
// Afterwards instead of issuing reset, this sequence continues to write to DAI interface.
// If any of the hardware partition is updated, then in next power cycle, the initialization will
// fail.
// This sequence will check the following items:
// - Otp_initialization failure triggers fatal alert
// - Status register reflect the correct error
// - Otp_ctrl's power init output stays 0

class otp_ctrl_init_fail_vseq extends otp_ctrl_smoke_vseq;
  `uvm_object_utils(otp_ctrl_init_fail_vseq)

  `uvm_object_new

  rand uint         num_to_lock_digests;
  bit [NumPart-1:0] init_err;

  constraint lock_digest_c {num_to_lock_digests < num_dai_op;}
  constraint num_iterations_c {num_dai_op inside {[20:100]};}

  virtual task pre_start();
    super.pre_start();
    num_to_lock_digests.rand_mode(0);
  endtask

  task body();
    for (uint i = 1; i <= num_dai_op; i++) begin
      bit [TL_DW-1:0] tlul_val;

      `DV_CHECK_RANDOMIZE_FATAL(this)

      // recalculate part_idx in case some test turn off constraint dai_wr_legal_addr_c
      part_idx = get_part_index(dai_addr);
      `uvm_info(`gfn, $sformatf("starting dai access seq %0d/%0d with addr %0h in partition %0d %0d",
                i, num_dai_op, dai_addr, part_idx, num_to_lock_digests), UVM_MEDIUM)

      // OTP write via DAI
      dai_wr(dai_addr, wdata0, wdata1);
      used_dai_addr_q.push_back(dai_addr);

      if (i > num_to_lock_digests && part_idx inside {[HwCfgIdx: Secret2Idx]}) begin
        init_err[part_idx] = 1;
      end

      // OTP read via DAI, check data in scb
      dai_rd_check(dai_addr, wdata0, wdata1);

      // If write sw partitions, check tlul window
      if (is_sw_part(dai_addr)) begin
        uvm_reg_addr_t tlul_addr = cfg.ral.get_addr_from_offset(get_sw_window_offset(dai_addr));
        tl_access(.addr(tlul_addr), .write(0), .data(tlul_val), .blocking(1), .check_rsp(1),
                  .check_exp_data(1), .exp_data(wdata0));
      end

      if (i == num_to_lock_digests) cal_hw_digests('1);

      csr_rd_check(.ptr(ral.status), .compare_value(1'b1 << OtpDaiIdleIdx));
    end

    do_otp_ctrl_init = 0;
    do_otp_pwr_init = (init_err == 0) ? 1 : 0;
    dut_init();

    if (init_err) begin
      bit [TL_DW-1:0] exp_status;

      cfg.otp_ctrl_vif.drive_pwr_otp_init(1);
      // Wait until OTP_INIT process the error
      wait(cfg.m_alert_agent_cfg["fatal_check_error"].vif.alert_tx_final.alert_p);
      check_fatal_alert_nonblocking("fatal_check_error");

      cfg.otp_ctrl_vif.drive_pwr_otp_init(0);

      // Wait until all partitions finish initialization
      cfg.clk_rst_vif.wait_clks($urandom_range(2000, 4000));

      foreach(init_err[i]) begin
        if (init_err[i]) exp_status |= 1'b1 << i;
      end
      csr_rd_check(.ptr(ral.status), .compare_value(exp_status));

      `DV_CHECK_EQ(cfg.otp_ctrl_vif.pwr_otp_done_o, 0)
      `DV_CHECK_EQ(cfg.otp_ctrl_vif.pwr_otp_idle_o, 0)

      // Issue reset to stop fatal alert
      dut_init();

    end else begin
      csr_rd_check(.ptr(ral.status), .compare_value(1'b1 << OtpDaiIdleIdx));
    end
  endtask
endclass
