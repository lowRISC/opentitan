// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otp_ctrl_common_vseq extends otp_ctrl_base_vseq;
  `uvm_object_utils(otp_ctrl_common_vseq)

  rand bit [TL_DW-1:0] dai_addr, wdata0, wdata1;
  rand port_drive_condition_e reset_drive_cond;

  string prim_otp_alert_name = "fatal_prim_otp_alert";
  string integ_err_alert_name = "fatal_bus_integ_error";

  // This flag is used to identify if the sec_cm or tl_intg_err uses prim_otp_tl_i/o.
  protected bit is_prim_otp;

  constraint dai_addr_c {
    dai_addr dist {
        [0 : (PartInfo[LifeCycleIdx].offset - 1)]    :/ 1,
        [PartInfo[LifeCycleIdx].offset : {11{1'b1}}] :/ 1};
  }

  constraint reset_drive_cond_c {
    reset_drive_cond dist {
        DriveRandomly      :/ 7,
        DuringOTPDaiBusy   :/ 1,
        DuringOTPRead      :/ 1,
        DuringOTPDaiDigest :/ 1
    };
  }

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    // drive dft_en pins to access the test_access memory
    cfg.otp_ctrl_vif.drive_lc_dft_en(lc_ctrl_pkg::On);
    // once turn on lc_dft_en regiser, will need some time to update the state register
    // two clock cycles for lc_async mode, one clock cycle for driving dft_en, one more clock cycle
    // so there is no racing condition.
    if (cfg.en_dv_cdc) cfg.clk_rst_vif.wait_clks(5);
    else               cfg.clk_rst_vif.wait_clks(3);
  endtask

  virtual task body();
    if (common_seq_type == "sec_cm_fi") begin
      // OTP_CTRL has many sec_cm items, so too many iterations of this test will consume too much
      // simulation time and eventually causes timeout. So we reduce to 10 iterations.
      run_sec_cm_fi_vseq(10);
    end else begin
      run_common_vseq_wrapper(num_trans);
    end
  endtask : body

  virtual task apply_resets_concurrently(int reset_duration_ps = 0);
    // For stress_all_with_rand_reset test only - backdoor clear OTP memory,
    // and re-initialize OTP_ctrl after reset.
    if (common_seq_type == "stress_all_with_rand_reset") begin
      cfg.otp_ctrl_vif.release_part_access_mubi();
      cfg.otp_ctrl_vif.drive_lc_escalate_en(lc_ctrl_pkg::Off);
      // Set dft_en to On to allow the csr_test to check all registers' default value after reset.
      cfg.otp_ctrl_vif.drive_lc_dft_en(lc_ctrl_pkg::On);
      otp_ctrl_init();
      otp_pwr_init();
      super.apply_resets_concurrently(reset_duration_ps);
      cfg.en_scb = 1;
    end else begin
      super.apply_resets_concurrently(reset_duration_ps);
    end
    clear_seq_flags();
  endtask

  virtual task wait_to_issue_reset(uint reset_delay_bound = 10_000_000);
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(reset_drive_cond)
    case (reset_drive_cond)
      DriveRandomly: begin
        super.wait_to_issue_reset(reset_delay_bound);
      end
      DuringOTPDaiBusy: begin
        `DV_SPINWAIT_EXIT(
            wait (do_otp_wr);
            cfg.clk_rst_vif.wait_clks($urandom_range(1, 70));,
            cfg.clk_rst_vif.wait_clks(reset_delay_bound);)
        #($urandom_range(0, cfg.clk_rst_vif.clk_period_ps) * 1ps);
      end
      DuringOTPDaiDigest: begin
        `DV_SPINWAIT_EXIT(
            wait (do_digest_cal);
            cfg.clk_rst_vif.wait_clks($urandom_range(1, 350));,
            cfg.clk_rst_vif.wait_clks(reset_delay_bound);)
        #($urandom_range(0, cfg.clk_rst_vif.clk_period_ps) * 1ps);
      end
      DuringOTPRead: begin
        `DV_SPINWAIT_EXIT(
            wait (do_otp_rd);
            cfg.clk_rst_vif.wait_clks($urandom_range(1, 10));,
            cfg.clk_rst_vif.wait_clks(reset_delay_bound);)
        #($urandom_range(0, cfg.clk_rst_vif.clk_period_ps) * 1ps);
      end
      default: `uvm_fatal(`gfn, $sformatf("Unsupported reset_drive_cond %0d", reset_drive_cond))
    endcase
  endtask : wait_to_issue_reset

  // This task overrides the check for `prim_onehot_check` and `tl_intg_error`.
  // Alerts coming from the `prim_otp` module will only bypass OTP_CTRL, it won't affect the
  // OTP_CTRL and will fire its own alerts.
  virtual task check_tl_intg_error_response();
    if (is_prim_otp) begin
      repeat ($urandom_range(5, 20)) begin
        wait_alert_trigger(prim_otp_alert_name, .wait_complete(1));
      end
    end else begin
      super.check_tl_intg_error_response();
    end
  endtask

  virtual task check_sec_cm_alert(string sec_type_name, string alert_name);
    `uvm_info(`gfn, $sformatf("expected fatal alert is triggered for %s",
              sec_type_name), UVM_LOW)

    // This is a fatal alert and design keeps sending it until reset is issued.
    // Check alerts are triggered for a few times
    repeat (5) begin
      wait_alert_trigger(alert_name, .wait_complete(1));
    end
  endtask

  // In tl_intg_err test, override this task to set is_prim_otp flag.
  virtual task run_tl_intg_err_vseq_sub(string ral_name);
    if (ral_name == "otp_ctrl_prim_reg_block") is_prim_otp = 1;
    else                                       is_prim_otp = 0;
    super.run_tl_intg_err_vseq_sub(ral_name);
  endtask

  virtual task check_sec_cm_fi_resp(sec_cm_base_if_proxy if_proxy);
    bit [TL_DW-1:0] exp_status_val, rdata0, rdata1;
    string prim_otp_alert_name = "fatal_prim_otp_alert";
    string integ_err_alert_name = "fatal_bus_integ_error";

    // Alerts coming from the `prim_otp` module will only bypass OTP_CTRL, it won't affect the
    // OTP_CTRL and will fire its own alerts.
    if (is_prim_otp) begin
      check_sec_cm_alert(if_proxy.sec_cm_type.name, prim_otp_alert_name);

    // Alerts coming from the `u_tlul_lc_gate` module will only trigger bus_integrity alerts, and
    // bus_integrity related status.
    // This error won't local escalate to OTP partitions.
    end else if (!uvm_re_match("*.u_tlul_lc_gate*", if_proxy.path)) begin
      check_sec_cm_alert(if_proxy.sec_cm_type.name, integ_err_alert_name);

      exp_status_val[OtpBusIntegErrorIdx] = 1;
      exp_status_val[OtpDaiIdleIdx] = 1;

    // All other errors triggers normal fatal alerts, and will locally escalate to other
    // partitions.
    end else begin
      super.check_sec_cm_fi_resp(if_proxy);

      // Set expected status error val.
      for (int i = 0; i <= OtpLciErrIdx; i++) exp_status_val[i] = 1;
      if (!uvm_re_match("*.u_otp_ctrl_lfsr_timer*", if_proxy.path)) begin
        exp_status_val[OtpLfsrFsmErrIdx] = 1;
      end else if (!uvm_re_match("*u_otp_ctrl_kdi*", if_proxy.path)) begin
        exp_status_val[OtpDerivKeyFsmErrIdx] = 1;
      end else if (!uvm_re_match("*u_otp_ctrl_scrmbl*", if_proxy.path)) begin
        exp_status_val[OtpScramblingFsmErrIdx] = 1;
      end

      csr_rd_check(.ptr(ral.status), .compare_value(exp_status_val), .err_msg(
                  $sformatf("cm_fi status failed at injection %0s", if_proxy.sec_cm_type.name)));

      // Check OTP is locked after fault error.
      `DV_CHECK_RANDOMIZE_FATAL(this)
      is_valid_dai_op = 0;

      // Access OTP via DAI interface.
      dai_wr(dai_addr, wdata0, wdata1);
      dai_rd(dai_addr, rdata0, rdata1);
      `DV_CHECK_EQ(rdata0, 0)
      `DV_CHECK_EQ(rdata1, 0)
      if (is_sw_part(dai_addr)) begin
        uvm_reg_addr_t tlul_addr = cfg.ral.get_addr_from_offset(get_sw_window_offset(dai_addr));
        tl_access(.addr(tlul_addr), .write(0), .data(rdata0), .blocking(1), .check_rsp(1),
                  .exp_err_rsp(1), .exp_data('1));
      end
      cal_hw_digests();
      write_sw_digests();

      // Access OTP via app interface.
      if ($urandom_range(0, 1)) req_otbn_key(0);
      if ($urandom_range(0, 1)) req_flash_addr_key(0);
      if ($urandom_range(0, 1)) req_flash_data_key(0);
      if ($urandom_range(0, 1)) req_all_sram_keys(0);
      cfg.clk_rst_vif.wait_clks($urandom_range(10, 20));

      csr_rd_check(.ptr(ral.status), .compare_value(exp_status_val),
                   .err_msg("status failure after OTP fatal fault error"));
    end
  endtask : check_sec_cm_fi_resp

  virtual function void sec_cm_fi_ctrl_svas(sec_cm_base_if_proxy if_proxy, bit enable);
    case (if_proxy.sec_cm_type)
      SecCmPrimCount: begin
        if (!enable) begin
          $assertoff(0, "tb.dut.gen_partitions[3].gen_buffered.u_part_buf.ScrmblDataKnown_A");
          $assertoff(0, "tb.dut.gen_partitions[4].gen_buffered.u_part_buf.ScrmblDataKnown_A");
          $assertoff(0, "tb.dut.gen_partitions[5].gen_buffered.u_part_buf.ScrmblDataKnown_A");
          $assertoff(0, "tb.dut.gen_partitions[6].gen_buffered.u_part_buf.ScrmblDataKnown_A");
          $assertoff(0, "tb.dut.gen_partitions[7].gen_lifecycle.u_part_buf.ScrmblDataKnown_A");
        end else begin
          $asserton(0, "tb.dut.gen_partitions[3].gen_buffered.u_part_buf.ScrmblDataKnown_A");
          $asserton(0, "tb.dut.gen_partitions[4].gen_buffered.u_part_buf.ScrmblDataKnown_A");
          $asserton(0, "tb.dut.gen_partitions[5].gen_buffered.u_part_buf.ScrmblDataKnown_A");
          $asserton(0, "tb.dut.gen_partitions[6].gen_buffered.u_part_buf.ScrmblDataKnown_A");
          $asserton(0, "tb.dut.gen_partitions[7].gen_lifecycle.u_part_buf.ScrmblDataKnown_A");
       end
      end
      SecCmPrimSparseFsmFlop, SecCmPrimDoubleLfsr, SecCmPrimOnehot: begin
        // No assertion error.
      end
      default: `uvm_fatal(`gfn, $sformatf("unexpected sec_cm_type %s", if_proxy.sec_cm_type.name))
    endcase

    // Set the flag to store if the error injection is on prim_tlul_if or core_tlul_if.
    if (!uvm_re_match("*.u_otp.*", if_proxy.path)) is_prim_otp = 1;
    else                                           is_prim_otp = 0;
  endfunction: sec_cm_fi_ctrl_svas

endclass
