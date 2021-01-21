// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aes_common_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new


  virtual task pre_start();
    do_aes_init = 1'b0;
    super.pre_start();
    cfg.en_scb = 0;
  endtask

  virtual function void shadow_reg_storage_err_post_write();
    void'(ral.status.alert_fatal_fault.predict(1));
  endfunction

  // for AES ctrl_shadowed register, the write transaction is valid only if the status is Idle
  // to ensure the shadow_reg_tests predict correct value, only write ctrl_shadowed when Idle
  virtual task shadow_reg_wr(dv_base_reg csr, uvm_reg_data_t wdata, output bit alert_triggered);
    bit [TL_DW-1:0] rdata;
    csr_rd(ral.status, rdata);
    if (get_field_val(ral.status.idle, rdata) == 1) begin
      super.shadow_reg_wr(csr, wdata, alert_triggered);
      // update predict value based on design
      ctrl_reg_map_invalid_value(wdata);
      csr.update_shadowed_val(wdata, 1);
    end
  endtask

  virtual function void ctrl_reg_map_invalid_value(ref bit [TL_DW-1:0] val);
    aes_mode_e      mode_e;
    key_len_e       key_len_e;
    bit [TL_DW-1:0] ctrl_shadowed_val;
    bit [TL_DW-1:0] operation_val = get_field_val(ral.ctrl_shadowed.operation, val);
    bit [TL_DW-1:0] mode_val = get_field_val(ral.ctrl_shadowed.mode, val);
    bit [TL_DW-1:0] key_len_val = get_field_val(ral.ctrl_shadowed.key_len, val);
    bit [TL_DW-1:0] manual_operation_val = get_field_val(ral.ctrl_shadowed.manual_operation, val);

    // construct
    ctrl_shadowed_val = get_csr_val_with_updated_field(ral.ctrl_shadowed.operation,
                                                       ctrl_shadowed_val, operation_val);
    ctrl_shadowed_val = get_csr_val_with_updated_field(ral.ctrl_shadowed.mode,
                                                       ctrl_shadowed_val, mode_val);
    ctrl_shadowed_val = get_csr_val_with_updated_field(ral.ctrl_shadowed.key_len,
                                                       ctrl_shadowed_val, key_len_val);
    ctrl_shadowed_val = get_csr_val_with_updated_field(ral.ctrl_shadowed.manual_operation,
                                                       ctrl_shadowed_val, manual_operation_val);

    if (!$cast(mode_e, mode_val)) begin
      ctrl_shadowed_val = get_csr_val_with_updated_field(ral.ctrl_shadowed.mode, ctrl_shadowed_val,
                                                         AES_NONE);
    end
    if (!$cast(key_len_e, key_len_val)) begin
      ctrl_shadowed_val = get_csr_val_with_updated_field(ral.ctrl_shadowed.key_len, ctrl_shadowed_val,
                                                         AES_256);
    end
    val = ctrl_shadowed_val;
  endfunction

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

endclass
