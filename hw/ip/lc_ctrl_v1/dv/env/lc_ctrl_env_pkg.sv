// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package lc_ctrl_env_pkg;
  // dep packages
  import uvm_pkg::*;
  import top_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import dv_base_reg_pkg::*;
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
  import kmac_app_agent_pkg::*;
  import lc_ctrl_dv_utils_pkg::*;
  import prim_mubi_pkg::MuBi8True;
  import sec_cm_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters
  parameter string LIST_OF_ALERTS[] = {
    "fatal_prog_error", "fatal_state_error", "fatal_bus_integ_error"
  };
  parameter uint NUM_ALERTS = 3;
  parameter uint CLAIM_TRANS_VAL = MuBi8True;
  parameter uint NUM_STATES = 24;

  // lc_otp_program host data width: lc_state_e width + lc_cnt_e width
  parameter uint OTP_PROG_HDATA_WIDTH = LcStateWidth + LcCountWidth;
  parameter uint OTP_PROG_DDATA_WIDTH = 1;

  // KMAC FSM state width
  parameter uint KMAC_FSM_WIDTH = 8;

  // Revision registers
  parameter uint LcCtrlSiliconCreatorId = `BUILD_SEED;
  parameter uint LcCtrlProductId = {LcCtrlSiliconCreatorId[30:0],
                                    (LcCtrlSiliconCreatorId[31] ^ LcCtrlSiliconCreatorId[30])};
  parameter uint LcCtrlRevisionId = {LcCtrlProductId[30:0],
                                    (LcCtrlProductId[31] ^ LcCtrlProductId[30])};

  typedef struct packed {
    lc_ctrl_pkg::lc_tx_t lc_dft_en_o;
    lc_ctrl_pkg::lc_tx_t lc_nvm_debug_en_o;
    lc_ctrl_pkg::lc_tx_t lc_hw_debug_en_o;
    lc_ctrl_pkg::lc_tx_t lc_cpu_en_o;
    lc_ctrl_pkg::lc_tx_t lc_creator_seed_sw_rw_en_o;
    lc_ctrl_pkg::lc_tx_t lc_owner_seed_sw_rw_en_o;
    lc_ctrl_pkg::lc_tx_t lc_seed_hw_rd_en_o;
    lc_ctrl_pkg::lc_tx_t lc_iso_part_sw_rd_en_o;
    lc_ctrl_pkg::lc_tx_t lc_iso_part_sw_wr_en_o;
    lc_ctrl_pkg::lc_tx_t lc_keymgr_en_o;
    lc_ctrl_pkg::lc_tx_t lc_escalate_en_o;
  } lc_outputs_t;

  // error injection
  typedef struct packed {
    // Bad protocol on clk_byp_ack_i
    bit clk_byp_error_rsp;
    // Bad protocol on flash_rma_ack_i
    bit flash_rma_error_rsp;
    // OTP responds with error
    bit otp_prog_err;
    // OTP data to lc_ctrl has error bit set
    bit otp_partition_err;
    // Incorrect token for state change
    bit token_mismatch_err;
    // Bit error in token from KMAC App interface
    bit token_invalid_err;
    // Error response from KMAC app
    bit token_response_err;
    // otp_lc_data_i.valid == 0
    bit otp_lc_data_i_valid_err;
    // Invalid state driven via OTP interface
    bit state_err;
    // Illegal (bad symbol encoding) state driven via OTP interface
    bit state_illegal_err;
    // Invalid count driven via OTP interface
    bit count_err;
    // Illegal (bad symbol encoding) count driven via OTP interface
    bit count_illegal_err;
    // Invalid LC fsm state - via force in lc_ctrl_if
    bit lc_fsm_backdoor_err;
    // Invalid KMAC IF fsm state - via force in lc_ctrl_if
    bit kmac_fsm_backdoor_err;
    // Invalid state - via force in lc_ctrl_if
    bit state_backdoor_err;
    // Invalid count - via force in lc_ctrl_if
    bit count_backdoor_err;
    // Send a transition request in post_trans state
    bit post_trans_err;
    // Invalid transition for current state
    bit transition_err;
    // Invalid transition because count already at maximum
    bit transition_count_err;
    // Randomly assert one or more escalate inputs
    bit security_escalation_err;
    // Use other than "Off" enum for MUBI input off values
    // clk_byp_rsp
    bit clk_byp_rsp_mubi_err;
    // flash_rma_rsp
    bit flash_rma_rsp_mubi_err;
    // OTP secrets valid
    bit otp_secrets_valid_mubi_err;
    // OTP test tokens valid
    bit otp_test_tokens_valid_mubi_err;
    // OTP RMA token valid
    bit otp_rma_token_valid_mubi_err;
    // Force bad values on token mux select lines
    bit token_mux_ctrl_redun_err;
    // Force bit errors in the token mux inputs
    bit token_mux_digest_err;
  } lc_ctrl_err_inj_t;

  // Test phase - used to synchronise the scoreboard
  typedef enum {
    LcCtrlTestInit,
    LcCtrlIterStart,
    LcCtrlLcInit,
    LcCtrlDutInitComplete,
    LcCtrlDutReady,
    LcCtrlBadNextState,
    LcCtrlWaitTransition,
    LcCtrlRandomEscalate,
    LcCtrlTransitionComplete,
    LcCtrlReadState1,
    LcCtrlEscalate,
    LcCtrlReadState2,
    LcCtrlPostTransition,
    LcCtrlPostTransTransitionComplete,
    LcCtrlPostStart
  } lc_ctrl_test_phase_e;

  // verilog_format: off
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
  // verilog_format: on

  // types
  typedef enum bit [1:0] {
    LcPwrInitReq,
    LcPwrIdleRsp,
    LcPwrDoneRsp,
    LcPwrIfWidth
  } lc_pwr_if_e;

  typedef virtual pins_if #(LcPwrIfWidth) pwr_lc_vif;
  typedef virtual lc_ctrl_if lc_ctrl_vif;

  // LC states which are valid for transitions
  const
  lc_state_e
  LcValidStateForTrans[] = '{
      LcStRaw,
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
      LcStRma
  };

  // CSR interfaces
  typedef enum {
    LcCtrlTLUL = 0,
    LcCtrlJTAG = 1
  } lc_ctrl_csr_intf_e;

  // functions
  function automatic bit valid_state_for_trans(lc_state_e curr_state);
    return (curr_state inside {LcValidStateForTrans});
  endfunction

  // verilog_format: off - avoid bad reformatting
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
  // verilog_format: on

  function automatic lc_ctrl_state_pkg::lc_token_t get_random_token();
    `DV_CHECK_STD_RANDOMIZE_FATAL(get_random_token,, "lc_ctrl_env_pkg");
  endfunction

  // package sources
  `include "lc_ctrl_parameters_cfg.sv"
  `include "lc_ctrl_env_cfg.sv"
  `include "lc_ctrl_env_cov.sv"
  `include "lc_ctrl_virtual_sequencer.sv"
  `include "lc_ctrl_scoreboard.sv"
  `include "lc_ctrl_env.sv"
  `include "lc_ctrl_vseq_list.sv"

endpackage
