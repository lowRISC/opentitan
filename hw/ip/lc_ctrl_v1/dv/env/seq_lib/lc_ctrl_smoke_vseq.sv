// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class lc_ctrl_smoke_vseq extends lc_ctrl_base_vseq;
  `uvm_object_utils(lc_ctrl_smoke_vseq)

  `uvm_object_new

  rand bit clk_byp_error_rsp, flash_rma_error_rsp;
  rand bit otp_prog_err, token_mismatch_err;
  dec_lc_state_e next_lc_state;
  rand lc_token_t token_scramble;

  constraint no_err_rsps_c {
    clk_byp_error_rsp == 0;
    flash_rma_error_rsp == 0;
  }

  constraint otp_prog_err_c {otp_prog_err == 0;}

  constraint token_mismatch_err_c {token_mismatch_err == 0;}

  virtual task pre_start();
    super.pre_start();
    add_otp_prog_err_bit();
    cfg.set_test_phase(LcCtrlTestInit);
    cfg.err_inj = 0;
  endtask

  virtual task post_start();
    // Kill sub processes
    disable run_clk_byp_rsp;
    disable run_flash_rma_rsp;
    super.post_start();
  endtask

  task body();

    fork
      run_clk_byp_rsp(clk_byp_error_rsp);
      run_flash_rma_rsp(flash_rma_error_rsp);
    join_none

    //
    // Check OTP read only regs (static ones)
    //
    read_otp_csrs();

    for (int i = 1; i <= num_trans; i++) begin
      cfg.set_test_phase(LcCtrlIterStart);
      if (i != 1) begin
        dut_init();
        // We expect initialized to be set to 1 after dut_init
        csr_rd_check(.ptr(ral.status.initialized), .compare_value(1));
      end
      `DV_CHECK_RANDOMIZE_FATAL(this)
      `uvm_info(`gfn, $sformatf(
                "starting seq %0d/%0d, init LC_state is %0s, LC_cnt is %0s",
                i,
                num_trans,
                lc_state.name,
                lc_cnt.name
                ), UVM_MEDIUM)

      if ($urandom_range(0, 1) && valid_state_for_trans(lc_state)) begin
        if (valid_state_for_trans(lc_state)) begin
          // We expect ready to be 1 when a non transition state is driven
          csr_rd_check(.ptr(ral.status.ready), .compare_value(1));
        end else begin
          // We expect ready to be 0 when a non transition state is driven
          csr_rd_check(.ptr(ral.status.ready), .compare_value(0));
        end
        rd_lc_state_and_cnt_csrs();
      end

      cfg.set_test_phase(LcCtrlDutReady);

      // SW transition request
      if (valid_state_for_trans(lc_state) && lc_cnt != LcCnt24) begin
        lc_ctrl_state_pkg::lc_token_t token_val = get_random_token();
        randomize_next_lc_state(dec_lc_state(lc_state));
        `uvm_info(`gfn, $sformatf(
                  "next_LC_state is %0s, input token is %0h", next_lc_state.name, token_val),
                  UVM_HIGH)

        set_hashed_token();
        cfg.set_test_phase(LcCtrlWaitTransition);
        sw_transition_req(next_lc_state, token_val);
        cfg.set_test_phase(LcCtrlTransitionComplete);
      end else begin
        // Test items that do not need a LC transition
        csr_wr(ral.claim_transition_if, CLAIM_TRANS_VAL);
        csr_wr(ral.transition_ctrl, $urandom_range(0, 1));
        cfg.set_test_phase(LcCtrlBadNextState);
        // wait at least two clks for scb to finish checking lc outputs
        cfg.clk_rst_vif.wait_clks($urandom_range(2, 10));
      end

      // Sample coverage if enabled
      sample_cov();

    end

  endtask : body

  // smoke test will always return valid next_lc_state
  // need to randomize here because associative array's index cannot be a rand input in constraint
  virtual function void randomize_next_lc_state(dec_lc_state_e curr_lc_state);
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(next_lc_state,
                                       next_lc_state inside {VALID_NEXT_STATES[curr_lc_state]};)
  endfunction

  // This function add otp_program_i's error bit field from the otp_prog_pull_agent device driver.
  // The pushed data length is (num_trans * 2) because for each transaction, we will have two
  // otp_program request at most (one for lc_token and one for lc_state)
  virtual function void add_otp_prog_err_bit();
    repeat (num_trans * 2) begin
      bit err_bit = otp_prog_err ? $urandom_range(0, 1) : 0;
      cfg.m_otp_prog_pull_agent_cfg.add_d_user_data(err_bit);
    end
  endfunction

  virtual function void set_hashed_token();
    lc_ctrl_pkg::token_idx_e token_idx = get_exp_token(dec_lc_state(lc_state), next_lc_state);
    kmac_pkg::rsp_digest_t kmac_digest;
    // No token for InvalidTokenIdx
    lc_ctrl_state_pkg::lc_token_t tokens_a[NumTokens-1];
    tokens_a[ZeroTokenIdx]       = lc_ctrl_state_pkg::AllZeroTokenHashed;
    tokens_a[RawUnlockTokenIdx]  = lc_ctrl_state_pkg::RndCnstRawUnlockTokenHashed;
    tokens_a[TestUnlockTokenIdx] = cfg.lc_ctrl_vif.otp_i.test_unlock_token;
    tokens_a[TestExitTokenIdx]   = cfg.lc_ctrl_vif.otp_i.test_exit_token;
    tokens_a[RmaTokenIdx]        = cfg.lc_ctrl_vif.otp_i.rma_token;

    `DV_CHECK_NE(token_idx, InvalidTokenIdx, $sformatf(
                 "curr_state: %0s, next_state %0s, does not expect InvalidToken",
                 lc_state.name,
                 next_lc_state.name
                 ))

    kmac_digest = token_to_kmac_digest(tokens_a[token_idx], token_scramble);
    clear_kmac_user_digest_share();
    cfg.m_kmac_app_agent_cfg.add_user_digest_share(kmac_digest);
  endfunction

endclass : lc_ctrl_smoke_vseq
