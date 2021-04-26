// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq
class lc_ctrl_smoke_vseq extends lc_ctrl_base_vseq;
  `uvm_object_utils(lc_ctrl_smoke_vseq)

  `uvm_object_new

  rand bit clk_byp_error_rsp;
  rand bit flash_rma_error_rsp;
  rand bit otp_prog_err;
  dec_lc_state_e next_lc_state;

  constraint no_err_rsps_c {
    clk_byp_error_rsp   == 0;
    flash_rma_error_rsp == 0;
  }

  constraint otp_prog_err_c {
    otp_prog_err == 0;
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
      `uvm_info(`gfn, $sformatf("starting seq %0d/%0d, init LC_state is %0s, LC_cnt is %0s",
                                i, num_trans, lc_state.name, lc_cnt.name), UVM_MEDIUM)

      if ($urandom_range(0, 1)) begin
        csr_rd_check(.ptr(ral.status.ready), .compare_value(1));
        rd_lc_state_and_cnt_csrs();
      end

      // SW transition request
      if (valid_state_for_trans(lc_state) && lc_cnt != LcCnt16) begin
        bit [TL_DW*4-1:0] token_val = {$urandom(), $urandom(), $urandom(), $urandom()};
        randomize_next_lc_state(dec_lc_state(lc_state));
        `uvm_info(`gfn, $sformatf("next_LC_state is %0s, input token is %0h", next_lc_state.name,
                                  token_val), UVM_DEBUG)

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
    // Raw Token
    if (lc_state == LcStRaw && next_lc_state inside {DecLcStTestUnlocked0,
        DecLcStTestUnlocked1, DecLcStTestUnlocked2, DecLcStTestUnlocked3}) begin
      cfg.m_otp_token_pull_agent_cfg.add_d_user_data(
          lc_ctrl_state_pkg::RndCnstRawUnlockTokenHashed);
    // RMA Token
    end else if (lc_state inside {LcStProd, LcStDev} && next_lc_state == DecLcStRma) begin
      cfg.m_otp_token_pull_agent_cfg.add_d_user_data(cfg.lc_ctrl_vif.otp_i.rma_token);
    // Test Exit Token
    end else if (lc_state inside {LcStTestUnlocked3, LcStTestLocked2, LcStTestUnlocked2,
                 LcStTestLocked1, LcStTestUnlocked1, LcStTestLocked0, LcStTestUnlocked0} &&
                 next_lc_state inside {DecLcStDev, DecLcStProd, DecLcStProdEnd}) begin
      cfg.m_otp_token_pull_agent_cfg.add_d_user_data(cfg.lc_ctrl_vif.otp_i.test_exit_token);
    // Test Unlock Token
    end else if ((lc_state == LcStTestLocked2 && next_lc_state == DecLcStTestUnlocked3) ||
                 (lc_state == LcStTestLocked1 && next_lc_state inside
                  {DecLcStTestUnlocked3, DecLcStTestUnlocked2}) ||
                 (lc_state == LcStTestLocked0 && next_lc_state inside
                  {DecLcStTestUnlocked3, DecLcStTestUnlocked2, DecLcStTestUnlocked1})) begin
      cfg.m_otp_token_pull_agent_cfg.add_d_user_data(cfg.lc_ctrl_vif.otp_i.test_unlock_token);
    // Test Zero Token
    end else begin
      cfg.m_otp_token_pull_agent_cfg.add_d_user_data(0);
    end
  endfunction
endclass : lc_ctrl_smoke_vseq
