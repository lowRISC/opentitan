// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// set volatile unlock to 1 and check if raw -> unlock0 transition is successful.
class lc_ctrl_volatile_unlock_smoke_vseq extends lc_ctrl_smoke_vseq;

  rand dec_lc_state_e next_state;
  rand bit next_state_is_testunlock0;

  `uvm_object_utils(lc_ctrl_volatile_unlock_smoke_vseq)
  `uvm_object_new

  constraint next_state_c {
      if (next_state_is_testunlock0) next_state == DecLcStTestUnlocked0;
      else next_state inside {LcValidTargetState};
      solve next_state_is_testunlock0 before next_state;
   }

  // Drive OTP input `lc_state` and `lc_cnt`.
  virtual task drive_otp_i(bit rand_otp_i = 1);
    `DV_CHECK_STD_RANDOMIZE_FATAL(lc_cnt)
    lc_state = LcStRaw;
    cfg.lc_ctrl_vif.init(.lc_state(lc_state), .lc_cnt(lc_cnt), .otp_device_id(cfg.otp_device_id),
                         .otp_manuf_state(cfg.otp_manuf_state),
                         .otp_vendor_test_status(cfg.otp_vendor_test_status));
  endtask

  task body();
    int lc_cnt_int;
    fork
      run_clk_byp_rsp(clk_byp_error_rsp);
      run_flash_rma_rsp(flash_rma_error_rsp);
    join_none

    `DV_CHECK_RANDOMIZE_FATAL(this)
    lc_cnt_int = dec_lc_cnt(lc_cnt);
    if (lc_cnt != LcCnt24) begin
      int exp_lc_cnt = lc_cnt_int == 0 ? 1 : lc_cnt_int;
      lc_ctrl_state_pkg::lc_token_t token_val = lc_ctrl_state_pkg::RndCnstRawUnlockTokenHashed;
      csr_wr(ral.claim_transition_if, CLAIM_TRANS_VAL);
      csr_wr(ral.transition_ctrl.volatile_raw_unlock, 1);
      csr_wr(ral.transition_target, {DecLcStateNumRep{next_state[DecLcStateWidth-1:0]}});
      foreach (ral.transition_token[i]) begin
        csr_wr(ral.transition_token[i], token_val[TL_DW-1:0]);
        token_val = token_val >> TL_DW;
      end
      csr_wr(ral.transition_cmd, 'h01);

      if (!`SEC_VOLATILE_RAW_UNLOCK_EN &&
          valid_raw_unlock_target_state(encode_lc_state(next_state))) begin
        // We expect the VOLATILE_RAW_UNLOCK bit to stay at zero in this case.
        cfg.clk_rst_vif.wait_clks(2);
        csr_rd_check(.ptr(ral.transition_ctrl.volatile_raw_unlock), .compare_value(0));
        cfg.clk_rst_vif.wait_clks(10);
        // Since we're performing a real transition in this case with a hashed token, we should
        // be getting a token error since a real transition expects an unhashed token.
        csr_spinwait(.ptr(ral.status.token_error), .exp_data(1), .timeout_ns(100_000));
        // The strap sampling override signal should be zero.
        `DV_CHECK_EQ(cfg.lc_ctrl_vif.strap_en_override_o, 0);
        if (cfg.en_cov) cov.volatile_raw_unlock_cg.sample(0);
      end else if (next_state == DecLcStTestUnlocked0) begin
        // We expect the VOLATILE_RAW_UNLOCK bit to go to one in this case.
        cfg.clk_rst_vif.wait_clks(2);
        csr_rd_check(.ptr(ral.transition_ctrl.volatile_raw_unlock), .compare_value(1));
        csr_spinwait(.ptr(ral.status.transition_successful), .exp_data(1), .timeout_ns(100_000));
        cfg.clk_rst_vif.wait_clks(10);
        `DV_CHECK_EQ(cfg.lc_ctrl_vif.strap_en_override_o, 1);
        csr_rd_check(.ptr(ral.lc_transition_cnt), .compare_value(exp_lc_cnt));
        csr_rd_check(.ptr(ral.lc_state),
                     .compare_value({DecLcStateNumRep{next_state[DecLcStateWidth-1:0]}}));
        if (cfg.en_cov) cov.volatile_raw_unlock_cg.sample(1);
        transition_to_next_valid_state(1);
      end else begin
        csr_spinwait(.ptr(ral.status.transition_error), .exp_data(1), .timeout_ns(100_000));
        `DV_CHECK_EQ(cfg.lc_ctrl_vif.strap_en_override_o, 0);
        if (cfg.en_cov) cov.volatile_raw_unlock_cg.sample(0);
      end
    end

  endtask : body

  virtual task transition_to_next_valid_state(bit volatile_raw_unlock_success);
    lc_ctrl_state_pkg::lc_token_t token_val = get_random_token();
    lc_ctrl_pkg::token_idx_e token;
    randomize_next_lc_state(next_state);
    lc_state = encode_lc_state(next_state);
    set_hashed_token();
    `uvm_info(`gfn, $sformatf("start another transition after volatile unlock: from %0s to %0s",
              next_state.name,  next_lc_state.name), UVM_LOW)
    sw_transition_req(next_lc_state, token_val);
    csr_spinwait(.ptr(ral.status.transition_successful), .exp_data(1), .timeout_ns(100_000));
  endtask

  virtual task sw_transition_req(bit [TL_DW-1:0] next_lc_state, bit [TL_DW*4-1:0] token_val);
    csr_wr(ral.claim_transition_if, CLAIM_TRANS_VAL);
    if ($urandom_range(0, 1)) csr_wr(ral.transition_ctrl, $urandom_range(0, 1));
    csr_wr(ral.transition_target, {DecLcStateNumRep{next_lc_state[DecLcStateWidth-1:0]}});
    foreach (ral.transition_token[i]) begin
      csr_wr(ral.transition_token[i], token_val[TL_DW-1:0]);
      token_val = token_val >> TL_DW;
    end

    // Execute transition
    csr_wr(ral.transition_cmd, 'h01);
  endtask
endclass : lc_ctrl_volatile_unlock_smoke_vseq
