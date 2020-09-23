// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Scrambling key derivation module for OTP.
//

`include "prim_assert.sv"

module otp_ctrl_kdi
  import otp_ctrl_pkg::*;
  import otp_ctrl_reg_pkg::*;
#(
  // Number of SRAM key requestor slots. All of them will use the same key seed.
  // However, each request will generate a new key seed.
  parameter int NumSramKeyReqSlots = 3
) (
  input                                              clk_i,
  input                                              rst_ni,
  // Pulse to enable this module after OTP partitions have
  // been initialized.
  input                                              key_deriv_en_i,
  // Escalation input. This moves the FSM into a terminal state.
  input  lc_tx_t                                     escalate_en_i,
  // FSM is in error state
  output otp_err_e                                   fsm_err_o,
  // Key seed inputs from OTP
  input  logic                                       scrmbl_key_seed_valid_i,
  input  logic [FlashKeySeedWidth-1:0]               flash_data_key_seed_i,
  input  logic [FlashKeySeedWidth-1:0]               flash_addr_key_seed_i,
  input  logic [SramKeySeedWidth-1:0]                sram_data_key_seed_i,
  // EDN interface for requesting entropy
  output otp_edn_req_t                               otp_edn_req_o,
  input  otp_edn_rsp_t                               otp_edn_rsp_i,
  // Lifecycle hashing request
  input  lc_otp_token_rsp_t                          lc_otp_token_req_i,
  output lc_otp_token_rsp_t                          lc_otp_token_rsp_o,
  // Scrambling key requests
  input  flash_otp_key_req_t                         flash_otp_key_req_i,
  output flash_otp_key_rsp_t                         flash_otp_key_rsp_o,
  input  sram_otp_key_req_t [NumSramKeyReqSlots-1:0] sram_otp_key_req_i,
  output sram_otp_key_rsp_t [NumSramKeyReqSlots-1:0] sram_otp_key_rsp_o,
  input  otbn_otp_key_req_t                          otbn_otp_key_req_i,
  output otbn_otp_key_rsp_t                          otbn_otp_key_rsp_o,
  // Scrambling mutex request
  output logic                                       scrmbl_mtx_req_o,
  input                                              scrmbl_mtx_gnt_i,
  // Scrambling datapath interface
  output otp_scrmbl_cmd_e                            scrmbl_cmd_o,
  output logic [ConstSelWidth-1:0]                   scrmbl_sel_o,
  output logic [ScrmblBlockWidth-1:0]                scrmbl_data_o,
  output logic                                       scrmbl_valid_o,
  input  logic                                       scrmbl_ready_i,
  input  logic                                       scrmbl_valid_i,
  input  logic [ScrmblBlockWidth-1:0]                scrmbl_data_i
);


endmodule : otp_ctrl_kdi
