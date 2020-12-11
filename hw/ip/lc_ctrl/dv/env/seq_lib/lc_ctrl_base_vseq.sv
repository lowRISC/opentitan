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

  rand lc_ctrl_pkg::lc_state_e lc_state;
  rand lc_ctrl_pkg::lc_cnt_e   lc_cnt;

  constraint lc_cnt_c {
    (lc_state != LcStRaw) -> (lc_cnt != LcCntRaw);
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
  virtual task lc_ctrl_init();
    `DV_CHECK_RANDOMIZE_FATAL(this)
    cfg.pwr_lc_vif.drive_pin(LcPwrInitReq, 1);
    cfg.lc_ctrl_vif.init(lc_state, lc_cnt);
    wait(cfg.pwr_lc_vif.pins[LcPwrDoneRsp] == 1);
    cfg.pwr_lc_vif.drive_pin(LcPwrInitReq, 0);
  endtask

  virtual task sw_transition_req(bit [TL_DW-1:0] next_lc_state, bit [TL_DW*3-1:0] token_val);
    csr_wr(ral.claim_transition_if, CLAIM_TRANS_VAL);
    csr_wr(ral.transition_target, next_lc_state);
    csr_wr(ral.transition_token_0, token_val[TL_DW-1:0]);
    csr_wr(ral.transition_token_1, token_val[TL_DW*2-1:TL_DW]);
    csr_wr(ral.transition_token_2, token_val[TL_DW*3-1:TL_DW*2]);
    csr_wr(ral.transition_cmd, 'h01);
    csr_spinwait(ral.status.transition_successful, 1);
  endtask

endclass : lc_ctrl_base_vseq
