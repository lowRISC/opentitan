// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// set volatile unlock to 1 and check if raw -> unlock0 transition is successful.
// TODO: csr checkings: include lc_cnt, and lc_state.
class lc_ctrl_volatile_unlock_smoke_vseq extends lc_ctrl_smoke_vseq;

  rand dec_lc_state_e next_state;
  rand bit next_state_is_testunlock0;

  `uvm_object_utils(lc_ctrl_volatile_unlock_smoke_vseq)
  `uvm_object_new

  constraint next_state_c {
      if (next_state_is_testunlock0) next_state == DecLcStTestUnlocked0;
      solve next_state_is_testunlock0 before next_state;
   }

  task body();
    fork
      run_clk_byp_rsp(clk_byp_error_rsp);
      run_flash_rma_rsp(flash_rma_error_rsp);
    join_none

    `DV_CHECK_RANDOMIZE_FATAL(this)
    drive_otp_i(0);
    if (lc_cnt != LcCnt24) begin
      lc_ctrl_state_pkg::lc_token_t token_val = lc_ctrl_state_pkg::RndCnstRawUnlockTokenHashed;
      csr_wr(ral.claim_transition_if, CLAIM_TRANS_VAL);
      csr_wr(ral.transition_ctrl.volatile_raw_unlock, 1);
      csr_wr(ral.transition_target, {DecLcStateNumRep{next_state[DecLcStateWidth-1:0]}});
      foreach (ral.transition_token[i]) begin
        csr_wr(ral.transition_token[i], token_val[TL_DW-1:0]);
        token_val = token_val >> TL_DW;
      end
      csr_wr(ral.transition_cmd, 'h01);

      if (next_state == DecLcStTestUnlocked0) begin
        csr_spinwait(.ptr(ral.status.transition_successful), .exp_data(1), .timeout_ns(100_000));
        cfg.clk_rst_vif.wait_clks(10);
        `DV_CHECK_EQ(cfg.lc_ctrl_vif.strap_en_override_o, 1);
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
