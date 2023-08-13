// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence will randomly issue lc_escalate_en during or after partition is locked.
// After lc_escalate_en is On, this sequence will continue run base sequence to check if all state
// machines are locked to `ErrorSt`.

class otp_ctrl_parallel_lc_esc_vseq extends otp_ctrl_dai_lock_vseq;
  `uvm_object_utils(otp_ctrl_parallel_lc_esc_vseq)

  `uvm_object_new

  rand port_drive_condition_e lc_esc_drive_cond;

  parameter int LC_ESC_MAX_CYCLE = 10_000;

  // This sequence will kill super.body sequence once lc_escalate_en is On. Disable these interface
  // requests to avoid sequencer error.
  constraint key_lc_reqs_c {
    do_req_keys == 0;
    do_lc_trans == 0;
  }

  virtual task body();
    fork
      begin : isolation_fork
        fork
          rand_wait_csr_no_outstanding();
          super.body();
        join_any;
        disable fork;
        set_lc_esc_and_check();
      end
    join
  endtask

  virtual task rand_wait_csr_no_outstanding();
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(lc_esc_drive_cond)
    wait(cfg.under_reset == 0);

    case (lc_esc_drive_cond)
      DriveRandomly: begin
        cfg.clk_rst_vif.wait_clks($urandom_range(0, LC_ESC_MAX_CYCLE));
      end
      DuringOTPInit: begin
        `DV_SPINWAIT_EXIT(
            wait (cfg.otp_ctrl_vif.pwr_otp_init_i == 1);
            cfg.clk_rst_vif.wait_clks($urandom_range(1, 20));,
            cfg.clk_rst_vif.wait_clks(LC_ESC_MAX_CYCLE);)
      end
      DuringOTPDaiBusy: begin
        `DV_SPINWAIT_EXIT(
            wait (do_otp_wr);
            cfg.clk_rst_vif.wait_clks($urandom_range(1, 70));,
            cfg.clk_rst_vif.wait_clks(LC_ESC_MAX_CYCLE);)
      end
      DuringOTPDaiDigest: begin
        `DV_SPINWAIT_EXIT(
            wait (do_digest_cal);
            cfg.clk_rst_vif.wait_clks($urandom_range(1, 500));,
            cfg.clk_rst_vif.wait_clks(LC_ESC_MAX_CYCLE);)
      end
      DuringOTPRead: begin
        `DV_SPINWAIT_EXIT(
            wait (do_otp_rd);
            cfg.clk_rst_vif.wait_clks($urandom_range(1, 10));,
            cfg.clk_rst_vif.wait_clks(LC_ESC_MAX_CYCLE);)
      end
      default: `uvm_fatal(`gfn, $sformatf("Unsupported lc_esc_drive_cond %0d", lc_esc_drive_cond))
    endcase

    wait_no_outstanding_access();
    wait (dai_wr_inprogress == 0);
  endtask

  virtual task set_lc_esc_and_check();
    // Random issue key requests before lc_esc_en is issued.
    randcase
      1: req_otbn_key(0);
      1: req_flash_addr_key(0);
      1: req_flash_data_key(0);
      1: req_all_sram_keys(0);
      1: req_lc_transition(0, 0);
    endcase

    if (lc_esc_drive_cond == DriveRandomly) cfg.clk_rst_vif.wait_clks($urandom_range(0, 50));

    if (!cfg.under_reset) cfg.otp_ctrl_vif.drive_lc_escalate_en(get_rand_lc_tx_val(.f_weight(0)));

    // Wait 5 clock cycles until async lc_escalate_en propogate to each state machine.
    cfg.clk_rst_vif.wait_clks(5);

    // After LC_escalate is On, we trigger the dai_lock_vseq to check interfaces will return
    // default values and the design won't hang.
    // This sequence will skip all the dut_init, and if reset is needed, the seq we will clear the
    // otp memories. Otherwise, if lc_esc is issued during OTP program, there might be ECC
    // uncorrectable errors and the OTP init will return an error.
    // The case `otp_init` errors are not handled by scb but checked via direct sequence.
    do_dut_init = 0;
    do_otp_ctrl_init = 1;
    super.body();
  endtask

  virtual task post_start();
    expect_fatal_alerts = 1;
    cfg.otp_ctrl_vif.drive_lc_escalate_en(lc_ctrl_pkg::Off);
    super.post_start();
  endtask
endclass
