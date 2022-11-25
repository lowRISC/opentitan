// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence triggers escalation by accumulating alerts in the same class.
// difference from smoke test, this sequence set the threshold to larger numbers.

class alert_handler_esc_fsm_sec_cm_vseq extends alert_handler_esc_alert_accum_vseq;
  `uvm_object_utils(alert_handler_esc_fsm_sec_cm_vseq)

  `uvm_object_new

  constraint esc_accum_thresh_c {
    foreach (accum_thresh[i]) {accum_thresh[i] inside {[0:10]};}
  }

  task body();
    // Disable all sec_cm proxies
    sec_cm_pkg::enable_sec_cm_if_proxy(uvm_glob_to_re("*"), 1'b0, 1'b1);
    // Enable esc_timer FSM sec_cm proxies
    sec_cm_pkg::enable_sec_cm_if_proxy(uvm_glob_to_re("*.gen_classes[*].u_esc_timer.u_state_regs"), 1'b1, 1'b1);

    fork
      super.body();
      run_common_vseq_wrapper(num_trans);
    join
  endtask : body

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
  endtask

  virtual task sec_cm_inject_fault(sec_cm_base_if_proxy if_proxy, output bit success);
    if (!uvm_re_match("tb.dut.u_ping_timer.*", if_proxy.path)) begin
      // Enable ping timer to get ping counter error
      csr_wr(ral.ping_timer_en_shadowed, 1);

      // Enable loc_alerts
      foreach (ral.loc_alert_en_shadowed[i]) csr_wr(ral.loc_alert_en_shadowed[i], 1);
    end
    super.sec_cm_inject_fault(if_proxy, success);
  endtask : sec_cm_inject_fault

  virtual task pre_run_sec_cm_fi_vseq();
    uvm_queue#(bit[9:0]) esc_timer_states = new;

    // Disable prim_sparse_fsm assertions.
    $assertoff(0, "tb.dut.gen_classes[0].u_esc_timer");
    $assertoff(0, "tb.dut.gen_classes[1].u_esc_timer");
    $assertoff(0, "tb.dut.gen_classes[2].u_esc_timer");
    $assertoff(0, "tb.dut.gen_classes[3].u_esc_timer");


    esc_timer_states.push_back(10'b1110000101);
    esc_timer_states.push_back(10'b0101010100);
    esc_timer_states.push_back(10'b0000011001);
    esc_timer_states.push_back(10'b1001100001);

    uvm_config_db#(uvm_queue#(bit[9:0]))::set(null, "*.gen_classes[*].u_esc_timer.*", "state_values", esc_timer_states);

    // Because the assertion contains `=>` statement.
    // Wait one clock cycle until the assertions are fully disabled.
    cfg.clk_rst_vif.wait_clks(1);
  endtask : pre_run_sec_cm_fi_vseq

  virtual task post_run_sec_cm_fi_vseq();
    // Enable prim_sparse_fsm assertions.
    $asserton(0, "tb.dut.gen_classes[0].u_esc_timer");
    $asserton(0, "tb.dut.gen_classes[1].u_esc_timer");
    $asserton(0, "tb.dut.gen_classes[2].u_esc_timer");
    $asserton(0, "tb.dut.gen_classes[3].u_esc_timer");
  endtask : post_run_sec_cm_fi_vseq

  // Override the task to check corresponding CSR status is updated correctly.
  virtual task check_tl_intg_error_response();
    bit exp_val = `gmv(ral.loc_alert_en_shadowed[LocalBusIntgFail]);
    csr_rd_check(.ptr(ral.loc_alert_cause[LocalBusIntgFail]), .compare_value(exp_val));
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
endclass : alert_handler_esc_fsm_sec_cm_vseq

