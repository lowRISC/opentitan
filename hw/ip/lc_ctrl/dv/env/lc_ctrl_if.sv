// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// interface for input data from OTP
interface lc_ctrl_if(input clk, input rst_n);

  import lc_ctrl_pkg::*;
  import lc_ctrl_state_pkg::*;
  import otp_ctrl_pkg::*;
  import otp_ctrl_part_pkg::*;

  logic tdo_oe; // TODO: add assertions
  otp_lc_data_t otp_i;
  otp_device_id_t otp_device_id_i;
  lc_token_t    hashed_token;

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

  lc_keymgr_div_t     keymgr_div_o;
  lc_flash_rma_seed_t flash_rma_seed_o;

  task automatic init(lc_state_e lc_state = LcStRaw,
                      lc_cnt_e   lc_cnt = LcCnt0,
                      lc_tx_t    clk_byp_ack = Off,
                      lc_tx_t    flash_rma_ack = Off);
    otp_i.valid = 1;
    otp_i.error = 0;
    otp_i.state = lc_state;
    otp_i.count = lc_cnt;
    otp_i.test_unlock_token = lc_ctrl_env_pkg::get_random_token();
    otp_i.test_exit_token   = lc_ctrl_env_pkg::get_random_token();
    otp_i.rma_token         = lc_ctrl_env_pkg::get_random_token();
    otp_i.id_state          = LcIdBlank;

    otp_device_id_i = 0;

    clk_byp_ack_i = clk_byp_ack;
    flash_rma_ack_i = flash_rma_ack;
  endtask

  task automatic set_clk_byp_ack(lc_tx_t val);
    clk_byp_ack_i = val;
  endtask

  task automatic set_flash_rma_ack(lc_tx_t val);
    flash_rma_ack_i = val;
  endtask

endinterface
