// Copyright lowRISC contributors (OpenTitan project).
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

  virtual task csr_wr_for_shadow_reg_predict(dv_base_reg    csr,
                                             uvm_reg_data_t wdata,
                                             bit            predict = 1);
    bit [TL_DW-1:0] rdata;
    if (csr.get_name() == "ctrl_shadowed" || csr.get_name() == "ctrl_gcm_shadowed") begin
      // Only update `ctrl_shadowed` and `ctrl_gcm_shadowed` register if AES is idle.
      // Use backdoor read because this sequence will run parallel with csr_rw.
      wait_no_outstanding_access();
      csr_rd(.ptr(ral.status), .value(rdata), .backdoor(1));
      if (get_field_val(ral.status.idle, rdata) == 1) begin
        csr_wr(.ptr(csr), .value(wdata), .en_shadow_wr(0), .predict(0));
        if (predict) begin
          if (csr.get_name() == "ctrl_shadowed") begin
            ctrl_reg_map_invalid_value(wdata);
          end else if (csr.get_name() == "ctrl_gcm_shadowed") begin
            // Depending on the currently configured GCM phase value, only a subset of new values
            // are allowed.
            csr_rd(.ptr(ral.ctrl_gcm_shadowed), .value(rdata), .backdoor(1));
            ctrl_gcm_reg_map_invalid_value(wdata, rdata);
          end
          void'(csr.predict(.value(wdata), .kind(UVM_PREDICT_WRITE)));
        end
        if (csr.get_name() == "ctrl_shadowed") begin
          // Only writing to `ctrl_shadowed` register can clear the update error status.
          if (csr.get_shadow_update_err() == 0 && csr.get_shadow_storage_err() == 0) begin
            clear_update_err_status();
          end
        end
      end
    end else begin
      super.csr_wr_for_shadow_reg_predict(csr, wdata, predict);
    end
  endtask

  virtual function void ctrl_reg_map_invalid_value(ref uvm_reg_data_t val);
    aes_mode_e      mode_e;
    key_len_e       key_len_e;
    prs_rate_e      prs_rate_e;
    bit [1:0]       aes_val = get_field_val(ral.ctrl_shadowed.operation, val);
    bit [TL_DW-1:0] mode_val = get_field_val(ral.ctrl_shadowed.mode, val);
    bit [TL_DW-1:0] key_len_val = get_field_val(ral.ctrl_shadowed.key_len, val);
    bit [TL_DW-1:0] prs_rate_val = get_field_val(ral.ctrl_shadowed.prng_reseed_rate, val);

    if (aes_val != 2'b10) aes_val = 2'b01;
    val = get_csr_val_with_updated_field(ral.ctrl_shadowed.operation, val, aes_val);

    if (!$cast(mode_e, mode_val)) begin
      val = get_csr_val_with_updated_field(ral.ctrl_shadowed.mode, val, AES_NONE);
    end

    if (!$cast(key_len_e, key_len_val)) begin
      val = get_csr_val_with_updated_field(ral.ctrl_shadowed.key_len, val, AES_256);
    end

    if (!$cast(prs_rate_e, prs_rate_val)) begin
      val = get_csr_val_with_updated_field(ral.ctrl_shadowed.prng_reseed_rate, val, PER_1);
    end
  endfunction

  virtual function void ctrl_gcm_reg_map_invalid_value(
      ref uvm_reg_data_t val,
      input ctrl_gcm_reg_t val_cur
  );
    ctrl_gcm_reg_t  ctrl_gcm_e;
    bit [AES_GCMPHASE_WIDTH-1:0] phase_val = get_field_val(ral.ctrl_gcm_shadowed.phase, val);
    bit [4:0] num_valid_bytes_val = get_field_val(ral.ctrl_gcm_shadowed.num_valid_bytes, val);

    if (`EN_GCM) begin
      // Resolve unsupported input values.
      if (!$cast(ctrl_gcm_e.phase, phase_val)) begin
        val = get_csr_val_with_updated_field(ral.ctrl_gcm_shadowed.phase, val, GCM_INIT);
        phase_val = get_field_val(ral.ctrl_gcm_shadowed.phase, val);
      end

      // Depending on the current phase, only a subset of next phases are allowed.
      if (val_cur.phase == GCM_INIT) begin
        if (phase_val != GCM_RESTORE &&
            phase_val != GCM_AAD     &&
            phase_val != GCM_TEXT    &&
            phase_val != GCM_TAG) begin
          phase_val = {val_cur.phase};
        end
      end else if (val_cur.phase == GCM_RESTORE) begin
        if (phase_val != GCM_INIT &&
            phase_val != GCM_AAD  &&
            phase_val != GCM_TEXT) begin
          phase_val = {val_cur.phase};
        end
      end else if (val_cur.phase == GCM_AAD) begin
        if (phase_val != GCM_INIT &&
            phase_val != GCM_TEXT &&
            phase_val != GCM_SAVE && // TODO: We can only enter GCM_SAVE after having done at least
                                     // one block. Right now, the DV cannot track this.
            phase_val != GCM_TAG) begin
          phase_val = {val_cur.phase};
        end
      end else if (val_cur.phase == GCM_TEXT) begin
        if (phase_val != GCM_INIT &&
            phase_val != GCM_SAVE && // TODO: We can only enter GCM_SAVE after having done at least
                                     // one block. Right now, the DV cannot track this.
            phase_val != GCM_TAG) begin
          phase_val = {val_cur.phase};
        end
      end else if (val_cur.phase == GCM_SAVE) begin
        if (phase_val != GCM_INIT) begin
          phase_val = {val_cur.phase};
        end
      end else if (val_cur.phase == GCM_TAG) begin
        if (phase_val != GCM_INIT) begin
          phase_val = {val_cur.phase};
        end
      end
    end else begin // EN_GCM == 0
      // The phase field is hardwired to GCM_INIT.
      phase_val = {GCM_INIT};
    end
    val = get_csr_val_with_updated_field(ral.ctrl_gcm_shadowed.phase, val, phase_val);

    if (num_valid_bytes_val == 5'd0 || num_valid_bytes_val > 5'd16 || `EN_GCM == 0) begin
      num_valid_bytes_val = 5'd16;
    end
    val = get_csr_val_with_updated_field(ral.ctrl_gcm_shadowed.num_valid_bytes, val,
        num_valid_bytes_val);
  endfunction

  // Any fatal error inside AES including storage errors inside any field of any shadow register
  // will completely lock up write access to the shadowed main control register (ctrl_shadowed)
  // and the shadowed GCM control register (ctrl_gcm_shadowed) until reset.
  // In contrast, the shadowed auxiliary control register behaves more like regular shadow
  // register:
  // - Fatal alerts inside AES don't generally block write access to the aux control register.
  // - A fatal storage error in one field of the shadowed aux control register doesn't block write
  //   access to other fields in the same register.
  //
  // For further details, refer to lowRISC/OpenTitan#8460 and lowRISC/OpenTitan#10617.
  virtual function void predict_shadow_reg_status(bit predict_update_err  = 0,
                                                  bit predict_storage_err = 0);
    super.predict_shadow_reg_status(predict_update_err, predict_storage_err);

    if (predict_storage_err) begin
      ral.ctrl_shadowed.lock_shadow_reg();
      ral.ctrl_gcm_shadowed.lock_shadow_reg();
    end
  endfunction

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

endclass
