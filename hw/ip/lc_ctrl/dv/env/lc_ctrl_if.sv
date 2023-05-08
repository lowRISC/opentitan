// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// interface for input data from OTP

`ifndef LC_CTRL_FSM_PATH
`define LC_CTRL_FSM_PATH tb.dut.u_lc_ctrl_fsm
`endif

interface lc_ctrl_if (
  input clk,
  input rst_n
);

  import uvm_pkg::*;
  import lc_ctrl_pkg::*;
  import lc_ctrl_state_pkg::*;
  import otp_ctrl_pkg::*;
  import otp_ctrl_part_pkg::*;

  `include "uvm_macros.svh"

  logic tdo_oe;
  otp_lc_data_t otp_i;
  otp_device_id_t otp_device_id_i = 0;
  otp_device_id_t otp_manuf_state_i = 0;
  lc_token_t hashed_token;
  prim_mubi_pkg::mubi4_t scanmode_i = prim_mubi_pkg::MuBi4False;
  logic scan_rst_ni = 1;
  lc_tx_t lc_dft_en_o;
  lc_tx_t lc_nvm_debug_en_o;
  lc_tx_t lc_hw_debug_en_o;
  lc_tx_t lc_cpu_en_o;
  lc_tx_t lc_creator_seed_sw_rw_en_o;
  lc_tx_t lc_owner_seed_sw_rw_en_o;
  lc_tx_t lc_iso_part_sw_rd_en_o;
  lc_tx_t lc_iso_part_sw_wr_en_o;
  lc_tx_t lc_seed_hw_rd_en_o;
  lc_tx_t lc_keymgr_en_o;
  lc_tx_t lc_escalate_en_o;
  lc_tx_t lc_check_byp_en_o;

  lc_tx_t clk_byp_req_o;
  lc_tx_t clk_byp_ack_i;
  lc_tx_t flash_rma_req_o;
  lc_tx_t flash_rma_ack_i;

  lc_keymgr_div_t keymgr_div_o;
  lc_flash_rma_seed_t flash_rma_seed_o;

  // OTP test signals
  logic [OtpTestCtrlWidth-1:0] otp_vendor_test_ctrl_o;
  logic [OtpTestStatusWidth-1:0] otp_vendor_test_status_i;

  logic strap_en_override_o;

  event lc_fsm_state_backdoor_write_ev;
  event lc_fsm_state_backdoor_read_ev;
  event kmac_fsm_state_backdoor_write_ev;
  event kmac_fsm_state_backdoor_read_ev;
  event state_backdoor_write_ev;
  event state_backdoor_read_ev;
  event count_backdoor_write_ev;
  event count_backdoor_read_ev;


  //
  // Whitebox signals - these come from within the RTL
  //

  // Decoded mutex claim signal for JTAG and TL
  logic mutex_claim_jtag;
  logic mutex_claim_tl;

  // FSM state
  lc_ctrl_pkg::fsm_state_e lc_ctrl_fsm_state;
  // Token mux control
  bit [TokenIdxWidth-1:0] token_idx0;
  bit [TokenIdxWidth-1:0] token_idx1;
  // Token Mux data
  lc_token_t hashed_token_i;
  lc_token_t hashed_token_mux;
  bit token_hash_ack_i;


  // Debug signals
  lc_ctrl_env_pkg::lc_ctrl_err_inj_t err_inj;
  lc_ctrl_env_pkg::lc_ctrl_test_phase_e test_phase;
  bit [79:0][7:0] test_sequence_typename;

  task automatic init(lc_state_e                     lc_state = LcStRaw,
                      lc_cnt_e                       lc_cnt = LcCnt0,
                      lc_tx_t                        clk_byp_ack = Off,
                      lc_tx_t                        flash_rma_ack = Off,
                      logic                          otp_partition_err = 0,
                      otp_device_id_t                otp_device_id = 0,
                      logic                          otp_lc_data_i_valid = 1,
                      otp_device_id_t                otp_manuf_state = 0,
                      logic [OtpTestStatusWidth-1:0] otp_vendor_test_status = 0,
                      lc_tx_t                        otp_secrets_valid = Off,
                      lc_tx_t                        otp_test_tokens_valid = On,
                      lc_tx_t                        otp_rma_token_valid = On);
    otp_i.valid             = otp_lc_data_i_valid;
    otp_i.error             = otp_partition_err;
    otp_i.state             = lc_state;
    otp_i.count             = lc_cnt;
    otp_i.test_unlock_token = lc_ctrl_env_pkg::get_random_token();
    otp_i.test_exit_token   = lc_ctrl_env_pkg::get_random_token();
    otp_i.rma_token         = lc_ctrl_env_pkg::get_random_token();
    otp_i.secrets_valid     = otp_secrets_valid;
    otp_i.test_tokens_valid = otp_test_tokens_valid;
    otp_i.rma_token_valid   = otp_rma_token_valid;


    clk_byp_ack_i           = clk_byp_ack;
    flash_rma_ack_i         = flash_rma_ack;

    // Make sure we get a transition
    fork
      begin
        @(posedge clk);
        otp_device_id_i          = otp_device_id;
        otp_manuf_state_i        = otp_manuf_state;
        otp_vendor_test_status_i = otp_vendor_test_status;
      end
    join_none

  endtask

  task automatic set_clk_byp_ack(lc_tx_t val);
    clk_byp_ack_i = val;
  endtask

  task automatic set_flash_rma_ack(lc_tx_t val);
    flash_rma_ack_i = val;
  endtask

  function automatic void clear_static_signals();
    otp_device_id_i = 0;
    otp_manuf_state_i = 0;
    otp_vendor_test_status_i = 0;
  endfunction

  function automatic void set_test_sequence_typename(string name);
    test_sequence_typename = name;
  endfunction

  function static void force_token_idx(input int idx, input logic [TokenIdxWidth-1:0] val);
    case (idx)
      0: force `LC_CTRL_FSM_PATH.token_idx0 = val;
      1: force `LC_CTRL_FSM_PATH.token_idx1 = val;
      default: begin
        `uvm_fatal($sformatf("%m"), $sformatf("force_token_idx: index %0d out of range", idx))
      end
    endcase
  endfunction

  function static void release_token_idx(input int idx);
    case (idx)
      0: release `LC_CTRL_FSM_PATH.token_idx0;
      1: release `LC_CTRL_FSM_PATH.token_idx1;
      default: begin
        `uvm_fatal($sformatf("%m"), $sformatf("release_token_idx: index %0d out of range", idx))
      end
    endcase
  endfunction

  function static void force_hashed_token(input int idx, input lc_token_t val);
    case (idx)
      0: force `LC_CTRL_FSM_PATH.hashed_token_i = val;
      1: force `LC_CTRL_FSM_PATH.hashed_token_mux = val;
      default: begin
        `uvm_fatal($sformatf("%m"), $sformatf("force_hashed_token: index %0d out of range", idx))
      end
    endcase
  endfunction

  function static void release_hashed_token(input int idx);
    case (idx)
      0: release `LC_CTRL_FSM_PATH.hashed_token_i;
      1: release `LC_CTRL_FSM_PATH.hashed_token_mux;
      default: begin
        `uvm_fatal($sformatf("%m"), $sformatf("release_hashed_token: index %0d out of range", idx))
      end
    endcase
  endfunction

endinterface

`undef LC_CTRL_FSM_PATH
