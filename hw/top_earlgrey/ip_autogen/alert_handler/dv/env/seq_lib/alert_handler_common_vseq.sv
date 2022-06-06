// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class alert_handler_common_vseq extends alert_handler_base_vseq;
  `uvm_object_utils(alert_handler_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }

  `uvm_object_new

  virtual task body();
    // run alert/esc ping response sequences without error or timeout to prevent triggering local
    // alert failure
    run_alert_ping_rsp_seq_nonblocking(0);
    run_esc_rsp_seq_nonblocking(0);
    run_common_vseq_wrapper(num_trans);
  endtask : body

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

  virtual task check_sec_cm_fi_resp(sec_cm_pkg::sec_cm_base_if_proxy if_proxy);
    if (!uvm_re_match("tb.dut.u_ping_timer.*", if_proxy.path)) begin
      // TODO:  check local alert regarding ping timeout triggered.
    end else begin
      foreach (cfg.esc_device_cfg[i]) begin
        `DV_CHECK_EQ(cfg.esc_device_cfg[i].vif.esc_tx.esc_p, 1,
                     $sformatf("escalation protocol_%0d is not set", i));
      end
    end
  endtask

  virtual task pre_run_sec_cm_fi_vseq();
    // Enable ping timer to get ping counter error
    csr_wr(ral.ping_timer_en_shadowed, 1);
  endtask : pre_run_sec_cm_fi_vseq
endclass
