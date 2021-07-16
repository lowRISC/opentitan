// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package lc_ctrl_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import tl_agent_pkg::*;
  import cip_base_pkg::*;
  import csr_utils_pkg::*;
  import lc_ctrl_ral_pkg::*;
  import lc_ctrl_pkg::*;
  import lc_ctrl_state_pkg::*;
  import otp_ctrl_pkg::*;
  import push_pull_agent_pkg::*;
  import alert_esc_agent_pkg::*;
  import jtag_riscv_agent_pkg::*;
  import lc_ctrl_dv_utils_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter string LIST_OF_ALERTS[] = {"fatal_prog_error",
                                       "fatal_state_error",
                                       "fatal_bus_integ_error"};
  parameter uint   NUM_ALERTS = 3;
  parameter uint   CLAIM_TRANS_VAL = 'ha5;
  parameter uint   NUM_STATES = 24;

  // lc_otp_program host data width: lc_state_e width + lc_cnt_e width
  parameter uint OTP_PROG_HDATA_WIDTH = LcStateWidth + LcCountWidth;
  parameter uint OTP_PROG_DDATA_WIDTH = 1;

  typedef struct packed {
    lc_ctrl_pkg::lc_tx_e lc_dft_en_o;
    lc_ctrl_pkg::lc_tx_e lc_nvm_debug_en_o;
    lc_ctrl_pkg::lc_tx_e lc_hw_debug_en_o;
    lc_ctrl_pkg::lc_tx_e lc_cpu_en_o;
    lc_ctrl_pkg::lc_tx_e lc_creator_seed_sw_rw_en_o;
    lc_ctrl_pkg::lc_tx_e lc_owner_seed_sw_rw_en_o;
    lc_ctrl_pkg::lc_tx_e lc_seed_hw_rd_en_o;
    lc_ctrl_pkg::lc_tx_e lc_iso_part_sw_rd_en_o;
    lc_ctrl_pkg::lc_tx_e lc_iso_part_sw_wr_en_o;
    lc_ctrl_pkg::lc_tx_e lc_keymgr_en_o;
    lc_ctrl_pkg::lc_tx_e lc_escalate_en_o;
  } lc_outputs_t;

  const lc_outputs_t EXP_LC_OUTPUTS[NUM_STATES] = {
    // Raw (fixed size array index 0)
    {Off, Off, Off, Off, Off, Off, Off, Off, Off, Off, Off},
    // TestUnlock0
    {On,  On,  On,  On,  Off, Off, Off, Off, On,  Off, Off},
    // TestLock0
    {Off, Off, Off, Off, Off, Off, Off, Off, Off, Off, Off},
    // TestUnlock1
    {On,  On,  On,  On,  Off, Off, Off, Off, On,  Off, Off},
    // TestLock1
    {Off, Off, Off, Off, Off, Off, Off, Off, Off, Off, Off},
    // TestUnlock2
    {On,  On,  On,  On,  Off, Off, Off, Off, On,  Off, Off},
    // TestLock2
    {Off, Off, Off, Off, Off, Off, Off, Off, Off, Off, Off},
    // TestUnlock3
    {On,  On,  On,  On,  Off, Off, Off, Off, On,  Off, Off},
    // TestLock3
    {Off, Off, Off, Off, Off, Off, Off, Off, Off, Off, Off},
    // TestUnlock4
    {On,  On,  On,  On,  Off, Off, Off, Off, On,  Off, Off},
    // TestLock4
    {Off, Off, Off, Off, Off, Off, Off, Off, Off, Off, Off},
    // TestUnlock5
    {On,  On,  On,  On,  Off, Off, Off, Off, On,  Off, Off},
    // TestLock5
    {Off, Off, Off, Off, Off, Off, Off, Off, Off, Off, Off},
    // TestUnlock6
    {On,  On,  On,  On,  Off, Off, Off, Off, On,  Off, Off},
    // TestLock6
    {Off, Off, Off, Off, Off, Off, Off, Off, Off, Off, Off},
    // TestUnlock7
    {On,  Off, On,  On,  Off, Off, Off, Off, On,  Off, Off},
    // Dev: lc_creator_seed_sw_rw_en_o (On if device is not personalized),
    // lc_seed_hw_rd_en_o (On if device is personalized)
    {Off, Off, On,  On,  On,  On,  On,  Off, On,  On,  Off},
    // Prod: lc_creator_seed_sw_rw_en_o (On if device is not personalized),
    // lc_seed_hw_rd_en_o (On if device is personalized)
    {Off, Off, Off, On,  On,  On,  On,  On,  On,  On,  Off},
    // ProdEnd: lc_creator_seed_sw_rw_en_o (On if device is not personalized),
    // lc_seed_hw_rd_en_o (On if device is personalized)
    {Off, Off, Off, On,  On,  On,  On,  On,  On,  On,  Off},
    // Rma
    {On,  On,  On,  On,  On,  On,  On,  On,  On,  On,  Off},
    // Scrap
    {Off, Off, Off, Off, Off, Off, Off, Off, Off, Off, On},
    // PostTrans
    {Off, Off, Off, Off, Off, Off, Off, Off, Off, Off, Off},
    // Escalate
    {Off, Off, Off, Off, Off, Off, Off, Off, Off, Off, On},
    // Invalid
    {Off, Off, Off, Off, Off, Off, Off, Off, Off, Off, On}
  };

  // types
  typedef enum bit [1:0] {
    LcPwrInitReq,
    LcPwrIdleRsp,
    LcPwrDoneRsp,
    LcPwrIfWidth
  } lc_pwr_if_e;

  typedef virtual pins_if #(LcPwrIfWidth) pwr_lc_vif;
  typedef virtual lc_ctrl_if              lc_ctrl_vif;

  // functions
  function automatic bit valid_state_for_trans(lc_state_e curr_state);
    return (curr_state inside {LcStRaw,
                               LcStTestUnlocked0,
                               LcStTestLocked0,
                               LcStTestUnlocked1,
                               LcStTestLocked1,
                               LcStTestUnlocked2,
                               LcStTestLocked2,
                               LcStTestUnlocked3,
                               LcStTestLocked3,
                               LcStTestUnlocked4,
                               LcStTestLocked4,
                               LcStTestUnlocked5,
                               LcStTestLocked5,
                               LcStTestUnlocked6,
                               LcStTestLocked6,
                               LcStTestUnlocked7,
                               LcStDev,
                               LcStProd,
                               LcStProdEnd,
                               LcStRma});
  endfunction

  function automatic lc_ctrl_pkg::token_idx_e get_exp_token(dec_lc_state_e curr_state,
                                                            dec_lc_state_e next_state);
    // Raw Token
    if (curr_state == DecLcStRaw && is_test_unlocked_state(next_state, 0, 7)) begin
      get_exp_token = lc_ctrl_pkg::RawUnlockTokenIdx;
    // RMA Token
    end else if (curr_state inside {DecLcStProd, DecLcStDev} && next_state == DecLcStRma) begin
      get_exp_token = lc_ctrl_pkg::RmaTokenIdx;
    // Test Exit Token
    end else if ((is_test_unlocked_state(curr_state, 0, 7) ||
                  is_test_locked_state(curr_state, 0, 6)) &&
                 next_state inside {DecLcStDev,
                                    DecLcStProd,
                                    DecLcStProdEnd}) begin
      get_exp_token = lc_ctrl_pkg::TestExitTokenIdx;
    // Test Unlock Token
    end else if ((curr_state == DecLcStTestLocked6 && is_test_unlocked_state(next_state, 7, 7)) ||
                 (curr_state == DecLcStTestLocked5 && is_test_unlocked_state(next_state, 6, 7)) ||
                 (curr_state == DecLcStTestLocked4 && is_test_unlocked_state(next_state, 5, 7)) ||
                 (curr_state == DecLcStTestLocked3 && is_test_unlocked_state(next_state, 4, 7)) ||
                 (curr_state == DecLcStTestLocked2 && is_test_unlocked_state(next_state, 3, 7)) ||
                 (curr_state == DecLcStTestLocked1 && is_test_unlocked_state(next_state, 2, 7)) ||
                 (curr_state == DecLcStTestLocked0 && is_test_unlocked_state(next_state, 1, 7)))
    begin
      get_exp_token = lc_ctrl_pkg::TestUnlockTokenIdx;
    // Test Zero Token
    end else if ((next_state == DecLcStScrap) ||
                 (is_test_unlocked_state(curr_state, 0, 7) && next_state == DecLcStRma) ||
                 (curr_state == DecLcStTestUnlocked6 && is_test_locked_state(next_state, 6, 6)) ||
                 (curr_state == DecLcStTestUnlocked5 && is_test_locked_state(next_state, 5, 6)) ||
                 (curr_state == DecLcStTestUnlocked4 && is_test_locked_state(next_state, 4, 6)) ||
                 (curr_state == DecLcStTestUnlocked3 && is_test_locked_state(next_state, 3, 6)) ||
                 (curr_state == DecLcStTestUnlocked2 && is_test_locked_state(next_state, 2, 6)) ||
                 (curr_state == DecLcStTestUnlocked1 && is_test_locked_state(next_state, 1, 6)) ||
                 (curr_state == DecLcStTestUnlocked0 && is_test_locked_state(next_state, 0, 6)))
    begin
      get_exp_token = lc_ctrl_pkg::ZeroTokenIdx;
    // Test Invalid Token
    end else begin
      get_exp_token = lc_ctrl_pkg::InvalidTokenIdx;
    end
  endfunction

  function automatic lc_ctrl_state_pkg::lc_token_t get_random_token();
    `DV_CHECK_STD_RANDOMIZE_FATAL(get_random_token, , "lc_ctrl_env_pkg");
  endfunction

  // package sources
  `include "lc_ctrl_env_cfg.sv"
  `include "lc_ctrl_env_cov.sv"
  `include "lc_ctrl_virtual_sequencer.sv"
  `include "lc_ctrl_scoreboard.sv"
  `include "lc_ctrl_env.sv"
  `include "lc_ctrl_vseq_list.sv"

endpackage
