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
  parameter int NumSramKeyReqSlots = 2
) (
  input                                              clk_i,
  input                                              rst_ni,
  // Pulse to enable this module after OTP partitions have
  // been initialized.
  input                                              key_deriv_en_i,
  // Escalation input. This moves the FSM into a terminal state.
  input  lc_tx_t                                     escalate_en_i,
  // FSM is in error state
  output logic                                       fsm_err_o,
  // Key seed inputs from OTP
  input  logic                                       scrmbl_key_seed_valid_i,
  input  logic [FlashKeySeedWidth-1:0]               flash_data_key_seed_i,
  input  logic [FlashKeySeedWidth-1:0]               flash_addr_key_seed_i,
  input  logic [SramKeySeedWidth-1:0]                sram_data_key_seed_i,
  // EDN interface for requesting entropy
  output logic                                       edn_req_o,
  input                                              edn_ack_i,
  input  [31:0]                                      edn_data_i,
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

  // tie-off and unused assignments for preventing lint messages
  assign fsm_err_o = 1'b0;
  assign edn_req_o = '0;
  assign lc_otp_token_rsp_o = '0;
  assign flash_otp_key_rsp_o = '0;
  assign sram_otp_key_rsp_o = '0;
  assign otbn_otp_key_rsp_o = '0;
  assign scrmbl_mtx_req_o = '0;
  assign scrmbl_cmd_o = '0;
  assign scrmbl_sel_o = '0;
  assign scrmbl_data_o = '0;
  assign scrmbl_valid_o = '0;

  logic unused_sigs_d, unused_sigs_q;
  assign unused_sigs_d = ^{key_deriv_en_i,
                           escalate_en_i,
                           scrmbl_key_seed_valid_i,
                           flash_data_key_seed_i,
                           flash_addr_key_seed_i,
                           sram_data_key_seed_i,
                           edn_ack_i,
                           edn_data_i,
                           lc_otp_token_req_i,
                           flash_otp_key_req_i,
                           sram_otp_key_req_i,
                           otbn_otp_key_req_i,
                           scrmbl_mtx_gnt_i,
                           scrmbl_ready_i,
                           scrmbl_valid_i,
                           scrmbl_data_i};

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      unused_sigs_q <= '0;
    end else begin
      unused_sigs_q <= unused_sigs_d;
    end
  end

endmodule : otp_ctrl_kdi
