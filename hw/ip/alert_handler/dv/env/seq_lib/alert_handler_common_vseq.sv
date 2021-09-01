// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class alert_handler_common_vseq extends alert_handler_base_vseq;
  `uvm_object_utils(alert_handler_common_vseq)

  rand bit entropy_bit;

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }

  `uvm_object_new

  virtual task body();
    // driven entropy to avoid assertion error in ping_timer
    cfg.entropy_vif.drive(entropy_bit);
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

endclass
