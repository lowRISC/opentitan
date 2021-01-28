// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class lc_ctrl_base_vseq extends cip_base_vseq #(
    .RAL_T               (lc_ctrl_reg_block),
    .CFG_T               (lc_ctrl_env_cfg),
    .COV_T               (lc_ctrl_env_cov),
    .VIRTUAL_SEQUENCER_T (lc_ctrl_virtual_sequencer)
  );
  `uvm_object_utils(lc_ctrl_base_vseq)

  // various knobs to enable certain routines
  bit do_lc_ctrl_init = 1'b1;

  rand lc_ctrl_state_pkg::lc_state_e lc_state;
  rand lc_ctrl_state_pkg::lc_cnt_e   lc_cnt;

  constraint lc_cnt_c {
    (lc_state != LcStRaw) -> (lc_cnt != LcCnt0);
  }

  `uvm_object_new

  virtual task pre_start();
    // LC_CTRL does not have interrupts
    do_clear_all_interrupts = 0;
    super.pre_start();
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_lc_ctrl_init) lc_ctrl_init();
  endtask

  virtual task dut_shutdown();
    // check for pending lc_ctrl operations and wait for them to complete
    // TODO
  endtask

  // setup basic lc_ctrl features
  virtual task lc_ctrl_init(bit rand_otp_i = 1);
    cfg.pwr_lc_vif.drive_pin(LcPwrInitReq, 1);
    if (rand_otp_i) begin
      `DV_CHECK_RANDOMIZE_FATAL(this)
    end else begin
      lc_state = LcStRaw;
      lc_cnt = LcCnt0;
    end
    cfg.lc_ctrl_vif.init(lc_state, lc_cnt);
    wait(cfg.pwr_lc_vif.pins[LcPwrDoneRsp] == 1);
    cfg.pwr_lc_vif.drive_pin(LcPwrInitReq, 0);
  endtask

  // some registers won't set to default value until otp_init is done
  virtual task read_and_check_all_csrs_after_reset();
    lc_ctrl_init(0);
    super.read_and_check_all_csrs_after_reset();
  endtask

  virtual task run_clk_byp_rsp_nonblocking(bit has_err = 0);
    fork
      forever begin
        lc_ctrl_pkg::lc_tx_t rsp;
        wait(cfg.lc_ctrl_vif.clk_byp_req_o == lc_ctrl_pkg::On);
        rsp = (has_err) ? $urandom_range(0, 1) ? lc_ctrl_pkg::On : lc_ctrl_pkg::Off :
                          lc_ctrl_pkg::On;
        cfg.clk_rst_vif.wait_clks($urandom_range(0, 20));
        cfg.lc_ctrl_vif.set_clk_byp_ack(rsp);

        wait (cfg.lc_ctrl_vif.clk_byp_req_o != lc_ctrl_pkg::On);
        rsp = (has_err) ? $urandom_range(0, 1) ? lc_ctrl_pkg::On : lc_ctrl_pkg::Off :
                          lc_ctrl_pkg::Off;
        cfg.clk_rst_vif.wait_clks($urandom_range(0, 20));
        cfg.lc_ctrl_vif.set_clk_byp_ack(rsp);
      end
    join_none
  endtask

  virtual task run_flash_rma_rsp_nonblocking(bit has_err = 0);
    fork
      forever begin
        lc_ctrl_pkg::lc_tx_t rsp;
        wait(cfg.lc_ctrl_vif.flash_rma_req_o == lc_ctrl_pkg::On);
        rsp = (has_err) ? $urandom_range(0, 1) ? lc_ctrl_pkg::On : lc_ctrl_pkg::Off :
                          lc_ctrl_pkg::On;
        cfg.clk_rst_vif.wait_clks($urandom_range(0, 20));
        cfg.lc_ctrl_vif.set_flash_rma_ack(rsp);

        wait (cfg.lc_ctrl_vif.flash_rma_req_o != lc_ctrl_pkg::On);
        rsp = (has_err) ? $urandom_range(0, 1) ? lc_ctrl_pkg::On : lc_ctrl_pkg::Off :
                          lc_ctrl_pkg::Off;
        cfg.clk_rst_vif.wait_clks($urandom_range(0, 20));
        cfg.lc_ctrl_vif.set_flash_rma_ack(rsp);
      end
    join_none
  endtask

  virtual task sw_transition_req(bit [TL_DW-1:0] next_lc_state,
                                 bit [TL_DW*4-1:0] token_val,
                                 bit trans_success = 1);
    csr_wr(ral.claim_transition_if, CLAIM_TRANS_VAL);
    csr_wr(ral.transition_target, next_lc_state);
    csr_wr(ral.transition_token_0, token_val[TL_DW-1:0]);
    csr_wr(ral.transition_token_1, token_val[TL_DW*2-1-:TL_DW]);
    csr_wr(ral.transition_token_2, token_val[TL_DW*3-1-:TL_DW]);
    csr_wr(ral.transition_token_3, token_val[TL_DW*4-1-:TL_DW]);
    csr_wr(ral.transition_cmd, 'h01);
    if (trans_success) begin
      csr_spinwait(ral.status.transition_successful, 1);
    end else begin
      // TODO: temp support only for otp_error
      csr_spinwait(ral.status.otp_error, 1);
      // always on alert, set time delay to make sure alert triggered for at least for one
      // handshake cycle
      cfg.clk_rst_vif.wait_clks($urandom_range(20, 50));
    end
  endtask

  // checking of these two CSRs are done in scb
  virtual task rd_lc_state_and_cnt_csrs();
    bit [TL_DW-1:0] val;
    csr_rd(ral.lc_state, val);
    csr_rd(ral.lc_transition_cnt, val);
  endtask

endclass : lc_ctrl_base_vseq
