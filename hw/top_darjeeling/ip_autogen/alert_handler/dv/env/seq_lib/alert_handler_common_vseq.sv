// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class alert_handler_common_vseq extends alert_handler_base_vseq;
  `uvm_object_utils(alert_handler_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }

  `uvm_object_new

  virtual task pre_start();
    super.pre_start();
    if (common_seq_type == "tl_intg_err") begin
      // If `en_csr_vseq_w_tl_intg = 1`, this vseq will check tl intg error won't affect any other
      // tl transaction.
      // If `en_csr_vseq_w_tl_intg = 0`, this vseq will check status, interrupts, and class_count
      // registers are updated correctly by DUT.
      en_csr_vseq_w_tl_intg = $urandom_range(0, 1);
      `uvm_info(`gfn, $sformatf("en_csr_vseq_w_tl_intg = %0b", en_csr_vseq_w_tl_intg), UVM_MEDIUM)
    end
  endtask

  virtual task body();
    // run alert/esc ping response sequences without error or timeout to prevent triggering local
    // alert failure
    run_esc_rsp_seq_nonblocking(0);
    run_common_vseq_wrapper(num_trans);
  endtask : body

  // If the tl_intg_err sequence does not run csr_rw in parallel, enable loc_alert error and enable
  // interrupts.
  // If the tl_intg_err sequence runs with csr_rw, do not enable loc_alert because it might trigger
  // escalation and affect register predications.
  virtual task run_tl_intg_err_vseq_sub(string ral_name);
    if (en_csr_vseq_w_tl_intg == 0) begin
      csr_wr(.ptr(ral.loc_alert_en_shadowed[LocalBusIntgFail]),
             .value($urandom_range(0, 1)),
             .predict(1));
      csr_wr(.ptr(ral.loc_alert_class_shadowed[LocalBusIntgFail]),
              .value($urandom_range(0, 3)),
              .predict(1));
      csr_wr(.ptr(ral.classa_ctrl_shadowed.en), .value(1));
      csr_wr(.ptr(ral.classb_ctrl_shadowed.en), .value(1));
      csr_wr(.ptr(ral.classc_ctrl_shadowed.en), .value(1));
      csr_wr(.ptr(ral.classd_ctrl_shadowed.en), .value(1));
    end
    super.run_tl_intg_err_vseq_sub(ral_name);
  endtask

  // Override the task to check corresponding CSR status is updated correctly.
  virtual task check_tl_intg_error_response();
    bit exp_val = `gmv(ral.loc_alert_en_shadowed[LocalBusIntgFail]);
    csr_rd_check(.ptr(ral.loc_alert_cause[LocalBusIntgFail]), .compare_value(exp_val));

    // Only check interrupt, accumlate count, and alert_cause registers if the local alert is
    // enabled.
    // However, this task does not check escalation port because the common escalation path is
    // checked in other tests that enabled scb.
    if (exp_val == 1) begin
      bit [TL_DW-1:0] class_i = `gmv(ral.loc_alert_class_shadowed[LocalBusIntgFail]);
      bit [TL_DW-1:0] accum_cnt;
      csr_rd_check(.ptr(ral.intr_state), .compare_value(1'b1 << class_i));
      case (class_i)
        0: csr_rd(.ptr(ral.classa_accum_cnt), .value(accum_cnt));
        1: csr_rd(.ptr(ral.classb_accum_cnt), .value(accum_cnt));
        2: csr_rd(.ptr(ral.classc_accum_cnt), .value(accum_cnt));
        3: csr_rd(.ptr(ral.classd_accum_cnt), .value(accum_cnt));
        default: `uvm_fatal(`gfn, $sformatf("Invalid class index %0d", class_i))
      endcase
      // Once tl_intg_err triggered, the error will be set to 1 until reset, so the counter will
      // continuously increment.
      `DV_CHECK_LT(0, accum_cnt, "Accumulated count should be larger than 0");
    end
  endtask

  // If the common sequence is tl integrity error sequence, we override this task to disable local
  // alert for tl_intg_err and lock this register. Because tl_intg_err can trigger local alert and
  // eventually triggers escalation. Then the auto predications for escalation related registers
  // such as `class_clr` and `clr_regwen` registers are not correct.
  virtual task run_csr_vseq(string csr_test_type,
                            int    num_test_csrs = 0,
                            bit    do_rand_wr_and_reset = 1,
                            dv_base_reg_block models[$] = {},
                            string ral_name = "");
    if (common_seq_type == "tl_intg_err") begin
      csr_wr(.ptr(ral.loc_alert_regwen[LocalBusIntgFail]), .value(0), .predict(1));
    end
    super.run_csr_vseq(csr_test_type, num_test_csrs, do_rand_wr_and_reset, models, ral_name);
  endtask

  virtual function void predict_shadow_reg_status(bit predict_update_err  = 0,
                                                  bit predict_storage_err = 0);
    if (predict_update_err) begin
      foreach (cfg.shadow_update_err_status_fields[status_field]) begin
        if (`gmv(ral.loc_alert_en_shadowed[LocalShadowRegUpdateErr])) begin
          void'(status_field.predict(cfg.shadow_update_err_status_fields[status_field]));
        end
      end
    end
    if (predict_storage_err) begin
      foreach (cfg.shadow_storage_err_status_fields[status_field]) begin
        if (`gmv(ral.loc_alert_en_shadowed[LocalShadowRegStorageErr])) begin
          void'(status_field.predict(cfg.shadow_storage_err_status_fields[status_field]));
        end
      end
    end
  endfunction

  virtual task check_sec_cm_fi_resp(sec_cm_base_if_proxy if_proxy);
    if (!uvm_re_match("tb.dut.u_ping_timer.*", if_proxy.path)) begin
      bit val;
      csr_rd(.ptr(ral.loc_alert_cause[LocalAlertPingFail]), .value(val));
      `DV_CHECK_EQ(val, 1, "local alert ping fail mismatch")
      csr_rd(.ptr(ral.loc_alert_cause[LocalEscPingFail]), .value(val));
      `DV_CHECK_EQ(val, 1, "local escalation ping fail mismatch")
    end else begin
      foreach (cfg.esc_device_cfg[i]) begin
        `DV_CHECK_EQ(cfg.esc_device_cfg[i].vif.esc_tx.esc_p, 1,
                     $sformatf("escalation protocol_%0d is not set", i));
      end
    end
    // Let the simulation wait a few clock cycles before reset to make sure assertions are checked.
    cfg.clk_rst_vif.wait_clks($urandom_range(2, 10));
  endtask

  virtual task sec_cm_inject_fault(sec_cm_base_if_proxy if_proxy);
    if (!uvm_re_match("tb.dut.u_ping_timer.*", if_proxy.path)) begin
      // Enable ping timer to get ping counter error
      csr_wr(ral.ping_timer_en_shadowed, 1);

      // Enable loc_alerts
      foreach (ral.loc_alert_en_shadowed[i]) csr_wr(ral.loc_alert_en_shadowed[i], 1);
    end
    super.sec_cm_inject_fault(if_proxy);
  endtask : sec_cm_inject_fault

  virtual task pre_run_sec_cm_fi_vseq();
    // Disable prim_sparse_fsm assertions.
    $assertoff(0, "tb.dut.gen_classes[0].u_esc_timer.CheckEn_A");
    $assertoff(0, "tb.dut.gen_classes[1].u_esc_timer.CheckEn_A");
    $assertoff(0, "tb.dut.gen_classes[2].u_esc_timer.CheckEn_A");
    $assertoff(0, "tb.dut.gen_classes[3].u_esc_timer.CheckEn_A");

    // Because the assertion contains `=>` statement.
    // Wait one clock cycle until the assertions are fully disabled.
    cfg.clk_rst_vif.wait_clks(1);
  endtask : pre_run_sec_cm_fi_vseq

  virtual task post_run_sec_cm_fi_vseq();
    // Enable prim_sparse_fsm assertions.
    $asserton(0, "tb.dut.gen_classes[0].u_esc_timer.CheckEn_A");
    $asserton(0, "tb.dut.gen_classes[1].u_esc_timer.CheckEn_A");
    $asserton(0, "tb.dut.gen_classes[2].u_esc_timer.CheckEn_A");
    $asserton(0, "tb.dut.gen_classes[3].u_esc_timer.CheckEn_A");
  endtask : post_run_sec_cm_fi_vseq

endclass
