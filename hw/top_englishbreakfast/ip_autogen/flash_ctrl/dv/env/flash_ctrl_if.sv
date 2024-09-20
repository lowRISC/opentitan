// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// interface for OTP, Life cycle, RMA, PWRMGR and KEYMGR
interface flash_ctrl_if (
  input logic clk,
  input logic rst_n
);

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

  lc_tx_t                           rma_req;
  lc_flash_rma_seed_t               rma_seed;
  lc_tx_t                           rma_ack;

  otp_ctrl_pkg::flash_otp_key_req_t otp_req;
  otp_ctrl_pkg::flash_otp_key_rsp_t otp_rsp;

  // JTAG
  logic                             cio_tck;
  logic                             cio_tms;
  logic                             cio_tdi;
  logic                             cio_tdo_en;
  logic                             cio_tdo;

  // power ready
  logic                             power_ready_h = 1'b1;

  // eviction
  logic [flash_ctrl_pkg::NumBanks-1:0][NumBuf-1:0] hazard;
  rd_buf_t [flash_ctrl_pkg::NumBanks-1:0][NumBuf-1:0] rd_buf;
  logic [flash_ctrl_pkg::NumBanks-1:0]             evict_prog;
  logic [flash_ctrl_pkg::NumBanks-1:0]             evict_erase;
  logic                                            fatal_err;

  // rma coverage
  logic       rd_buf_en;
  rma_state_e rma_state;
  logic [10:0] prog_state0;
  logic [10:0] prog_state1;
  logic [10:0] lcmgr_state;
  logic        init;
  logic        hw_rvalid;

  // v2s error injection
  logic        host_gnt;
  logic ctrl_fsm_idle;
  logic [1:0] host_outstanding;

  // Time to wait from reset assertion to power-down assertion. Default is 0.
  // Defined here so it will be accessible by both the TB and the env cfg.
  int unsigned rst_to_pd_time_ns = 0;

  clocking cb @(posedge clk);
    default input #1step output #2;
    output    rma_req, rma_seed;
    input     rma_ack;
  endclocking
endinterface : flash_ctrl_if
