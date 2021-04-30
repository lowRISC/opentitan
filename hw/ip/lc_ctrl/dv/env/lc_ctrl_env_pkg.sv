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

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter string LIST_OF_ALERTS[] = {"fatal_prog_error", "fatal_state_error"};
  parameter uint   NUM_ALERTS = 2;
  parameter uint   CLAIM_TRANS_VAL = 'ha5;
  parameter uint   NUM_STATES = 16;

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
    // Dev: lc_creator_seed_sw_rw_en_o (On if device is not personalized),
    // lc_seed_hw_rd_en_o (On if device is personalized)
    {Off, Off, On,  On,  On,  On,  On,  On,  On,  On,  Off},
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
    {Off, Off, Off, Off, Off, Off, Off, Off, Off, Off, On},
    // Escalate
    {Off, Off, Off, Off, Off, Off, Off, Off, Off, Off, On},
    // Invalid
    {Off, Off, Off, Off, Off, Off, Off, Off, Off, Off, On}
  };

  // associative array cannot declare parameter here, so we used const instead
  const dec_lc_state_e VALID_NEXT_STATES [dec_lc_state_e][$] = '{
    DecLcStRma:     {DecLcStScrap},
    DecLcStProdEnd: {DecLcStScrap},
    DecLcStProd:    {DecLcStScrap, DecLcStRma},
    DecLcStDev:     {DecLcStScrap, DecLcStRma},
    DecLcStTestUnlocked3: {DecLcStScrap, DecLcStRma, DecLcStProdEnd, DecLcStProd, DecLcStDev},
    DecLcStTestUnlocked2: {DecLcStScrap, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                           DecLcStTestLocked2},
    DecLcStTestUnlocked1: {DecLcStScrap, DecLcStRma, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                           DecLcStTestLocked2, DecLcStTestLocked1},
    DecLcStTestUnlocked0: {DecLcStScrap, DecLcStRma, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                           DecLcStTestLocked2, DecLcStTestLocked1, DecLcStTestLocked0},
    DecLcStTestLocked2: {DecLcStScrap, DecLcStProdEnd, DecLcStProd,
                         DecLcStDev, DecLcStTestUnlocked3},
    DecLcStTestLocked1: {DecLcStScrap, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                         DecLcStTestUnlocked3, DecLcStTestUnlocked2},
    DecLcStTestLocked0: {DecLcStScrap, DecLcStProdEnd, DecLcStProd, DecLcStDev,
                         DecLcStTestUnlocked3, DecLcStTestUnlocked2, DecLcStTestUnlocked1},
    DecLcStRaw: {DecLcStScrap, DecLcStTestUnlocked2, DecLcStTestUnlocked1, DecLcStTestUnlocked0}
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
    valid_state_for_trans = 0;
    if (curr_state inside {LcStRma, LcStProdEnd, LcStProd, LcStDev, LcStTestUnlocked3,
                           LcStTestUnlocked2, LcStTestUnlocked1, LcStTestUnlocked0,
                           LcStTestLocked2, LcStTestLocked1, LcStTestLocked0, LcStRaw}) begin
      valid_state_for_trans = 1;
    end
  endfunction

  function automatic dec_lc_state_e dec_lc_state(lc_state_e curr_state);
    case (curr_state)
      LcStRaw:           return DecLcStRaw;
      LcStTestUnlocked0: return DecLcStTestUnlocked0;
      LcStTestLocked0:   return DecLcStTestLocked0;
      LcStTestUnlocked1: return DecLcStTestUnlocked1;
      LcStTestLocked1:   return DecLcStTestLocked1;
      LcStTestUnlocked2: return DecLcStTestUnlocked2;
      LcStTestLocked2:   return DecLcStTestLocked2;
      LcStTestUnlocked3: return DecLcStTestUnlocked3;
      LcStDev:           return DecLcStDev;
      LcStProd:          return DecLcStProd;
      LcStProdEnd:       return DecLcStProdEnd;
      LcStRma:           return DecLcStRma;
      LcStScrap:         return DecLcStScrap;
      default: `uvm_fatal("lc_env_pkg", $sformatf("unknown lc_state 0x%0h", curr_state))
    endcase
  endfunction

  function automatic int dec_lc_cnt(lc_cnt_e curr_cnt);
    case (curr_cnt)
      LcCnt0  : return 0;
      LcCnt1  : return 1;
      LcCnt2  : return 2;
      LcCnt3  : return 3;
      LcCnt4  : return 4;
      LcCnt5  : return 5;
      LcCnt6  : return 6;
      LcCnt7  : return 7;
      LcCnt8  : return 8;
      LcCnt9  : return 9;
      LcCnt10 : return 10;
      LcCnt11 : return 11;
      LcCnt12 : return 12;
      LcCnt13 : return 13;
      LcCnt14 : return 14;
      LcCnt15 : return 15;
      LcCnt16 : return 16;
      default: `uvm_fatal("lc_env_pkg", $sformatf("unknown lc_cnt 0x%0h", curr_cnt))
    endcase
  endfunction

  function automatic lc_ctrl_pkg::token_idx_e get_exp_token(dec_lc_state_e curr_state,
                                                            dec_lc_state_e next_state);
    // Raw Token
    if (curr_state == DecLcStRaw && next_state inside {DecLcStTestUnlocked0,
        DecLcStTestUnlocked1, DecLcStTestUnlocked2, DecLcStTestUnlocked3}) begin
      get_exp_token = lc_ctrl_pkg::RawUnlockTokenIdx;
    // RMA Token
    end else if (curr_state inside {DecLcStProd, DecLcStDev} && next_state == DecLcStRma) begin
      get_exp_token = lc_ctrl_pkg::RmaTokenIdx;
    // Test Exit Token
    end else if (curr_state inside {DecLcStTestUnlocked3, DecLcStTestLocked2, DecLcStTestUnlocked2,
                 DecLcStTestLocked1, DecLcStTestUnlocked1, DecLcStTestLocked0,
                 DecLcStTestUnlocked0} &&
                 next_state inside {DecLcStDev, DecLcStProd, DecLcStProdEnd}) begin
      get_exp_token = lc_ctrl_pkg::TestExitTokenIdx;
    // Test Unlock Token
    end else if ((curr_state == DecLcStTestLocked2 && next_state == DecLcStTestUnlocked3) ||
                 (curr_state == DecLcStTestLocked1 && next_state inside
                     {DecLcStTestUnlocked3, DecLcStTestUnlocked2}) ||
                 (curr_state == DecLcStTestLocked0 && next_state inside
                     {DecLcStTestUnlocked3, DecLcStTestUnlocked2, DecLcStTestUnlocked1})) begin
      get_exp_token = lc_ctrl_pkg::TestUnlockTokenIdx;
    // Test Zero Token
    end else if (next_state == DecLcStScrap ||
                 (curr_state inside {DecLcStTestUnlocked3, DecLcStTestUnlocked2,
                     DecLcStTestUnlocked1, DecLcStTestUnlocked0} && next_state == DecLcStRma) ||
                 (curr_state == DecLcStTestUnlocked2 && next_state == DecLcStTestLocked2) ||
                 (curr_state ==  DecLcStTestUnlocked1 && next_state inside {DecLcStTestLocked2,
                     DecLcStTestLocked1}) ||
                 (curr_state ==  DecLcStTestUnlocked0 && next_state inside {DecLcStTestLocked2,
                     DecLcStTestLocked1, DecLcStTestLocked0})) begin
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
