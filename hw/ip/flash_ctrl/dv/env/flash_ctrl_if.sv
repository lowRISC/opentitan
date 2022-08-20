// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// interface for OTP, Life cycle, RMA, PWRMGR and KEYMGR
interface flash_ctrl_if ();

  import lc_ctrl_pkg::*;
  import pwrmgr_pkg::*;
  import flash_ctrl_pkg::*;
  import flash_phy_pkg::*;
  import otp_ctrl_pkg::*;
  import ast_pkg::*;

  lc_tx_t                           lc_creator_seed_sw_rw_en = lc_ctrl_pkg::Off;
  lc_tx_t                           lc_owner_seed_sw_rw_en = lc_ctrl_pkg::Off;
  lc_tx_t                           lc_seed_hw_rd_en = lc_ctrl_pkg::On;

  lc_tx_t                           lc_iso_part_sw_rd_en = lc_ctrl_pkg::Off;
  lc_tx_t                           lc_iso_part_sw_wr_en = lc_ctrl_pkg::Off;

  lc_tx_t                           lc_nvm_debug_en = lc_ctrl_pkg::Off;
  lc_tx_t                           lc_escalate_en = lc_ctrl_pkg::Off;

  pwr_flash_t                       pwrmgr;

  keymgr_flash_t                    keymgr;

  lc_tx_t                           rma_req = lc_ctrl_pkg::Off;
  lc_flash_rma_seed_t               rma_seed = LC_FLASH_RMA_SEED_DEFAULT;
  lc_tx_t                           rma_ack;

  otp_ctrl_pkg::flash_otp_key_req_t otp_req;
  otp_ctrl_pkg::flash_otp_key_rsp_t otp_rsp;

  // JTAG
  logic                             cio_tck;
  logic                             cio_tms;
  logic                             cio_tdi;
  logic                             cio_tdo_en;
  logic                             cio_tdo;

  // alert
  ast_dif_t                         flash_alert;

  // power ready
  logic                             power_ready_h = 1'b1;

  // eviction
  logic [flash_ctrl_pkg::NumBanks-1:0][NumBuf-1:0] hazard;
  rd_buf_t [flash_ctrl_pkg::NumBanks-1:0][NumBuf-1:0] rd_buf;
  logic [flash_ctrl_pkg::NumBanks-1:0]             evict_prog;
  logic [flash_ctrl_pkg::NumBanks-1:0]             evict_erase;
  logic                                            fatal_err;

endinterface : flash_ctrl_if
