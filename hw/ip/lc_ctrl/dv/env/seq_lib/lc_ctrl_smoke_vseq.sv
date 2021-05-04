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

  constraint no_err_rsps_c {
    clk_byp_error_rsp   == 0;
    flash_rma_error_rsp == 0;
  }

  constraint otp_prog_err_c {
    otp_prog_err == 0;
  }

  constraint token_mismatch_err_c {
    token_mismatch_err == 0;
  }

  virtual task pre_start();
    super.pre_start();
    add_otp_prog_err_bit();
  endtask

  task body();
    run_clk_byp_rsp_nonblocking(clk_byp_error_rsp);
    run_flash_rma_rsp_nonblocking(flash_rma_error_rsp);

    for (int i = 1; i <= num_trans; i++) begin
      if (i != 1) dut_init();
      `DV_CHECK_RANDOMIZE_FATAL(this)
      `uvm_info(`gfn, $sformatf("starting seq %0d/%0d, init LC_state is %0s, LC_cnt is %0s",
                                i, num_trans, lc_state.name, lc_cnt.name), UVM_MEDIUM)

      if ($urandom_range(0, 1)) begin
        csr_rd_check(.ptr(ral.status.ready), .compare_value(1));
        rd_lc_state_and_cnt_csrs();
      end

      // SW transition request
      if (valid_state_for_trans(lc_state) && lc_cnt != LcCnt16) begin
        lc_ctrl_state_pkg::lc_token_t token_val = get_random_token();
        randomize_next_lc_state(dec_lc_state(lc_state));
        `uvm_info(`gfn, $sformatf("next_LC_state is %0s, input token is %0h", next_lc_state.name,
                                  token_val), UVM_HIGH)

        set_hashed_token();
        sw_transition_req(next_lc_state, token_val);
      end else begin
        // wait at least two clks for scb to finish checking lc outputs
        cfg.clk_rst_vif.wait_clks($urandom_range(2, 10));
      end
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

    // No token for InvalidTokenIdx
    lc_ctrl_state_pkg::lc_token_t tokens_a [NumTokens-1];
    tokens_a[ZeroTokenIdx]       = 0;
    tokens_a[RawUnlockTokenIdx]  = lc_ctrl_state_pkg::RndCnstRawUnlockTokenHashed;
    tokens_a[TestUnlockTokenIdx] = cfg.lc_ctrl_vif.otp_i.test_unlock_token;
    tokens_a[TestExitTokenIdx]   = cfg.lc_ctrl_vif.otp_i.test_exit_token;
    tokens_a[RmaTokenIdx]        = cfg.lc_ctrl_vif.otp_i.rma_token;

    `DV_CHECK_NE(token_idx, InvalidTokenIdx,
                 $sformatf("curr_state: %0s, next_state %0s, does not expect InvalidToken",
                           lc_state.name, next_lc_state.name))

    // Clear the user_data_q here cause previous data might not be used due to some other lc_ctrl
    // error: for example: lc_program error
    cfg.m_otp_token_pull_agent_cfg.clear_d_user_data();
    if (!token_mismatch_err) begin
      cfg.m_otp_token_pull_agent_cfg.add_d_user_data(tokens_a[token_idx]);
    end else begin
      // 50% chance to input other token data, 50% chance let push-pull agent drive random data
      if ($urandom_range(0, 1)) begin
        token_idx = $urandom_range(0, TokenIdxWidth-2);
        cfg.m_otp_token_pull_agent_cfg.add_d_user_data(tokens_a[token_idx]);
      end
    end
  endfunction
endclass : lc_ctrl_smoke_vseq
