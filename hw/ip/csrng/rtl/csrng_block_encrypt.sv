// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: AES-based block encrypt module for CSRNG
//

module csrng_block_encrypt import csrng_pkg::*; #(
  parameter aes_pkg::sbox_impl_e SBoxImpl = aes_pkg::SBoxImplLut
) (
  input  logic              clk_i,
  input  logic              rst_ni,

  // Global enable
  input  logic              enable_i,

  // Request from ctr_drbg
  input  logic              req_vld_i,
  output logic              req_rdy_o,
  input  csrng_key_v_t      req_data_i,

  // Response to ctr_drbg
  output logic              rsp_vld_o,
  input  logic              rsp_rdy_i,
  output logic [BlkLen-1:0] rsp_data_o,

  // Status and error signals
  output logic              cipher_sm_err_o
);

  localparam int unsigned NumShares = 1;

  // Signals
  aes_pkg::sp2v_e       cipher_in_valid;
  aes_pkg::sp2v_e       cipher_in_ready;
  aes_pkg::sp2v_e       cipher_out_valid;
  aes_pkg::sp2v_e       cipher_out_ready;

  logic [3:0][3:0][7:0] state_init[NumShares];

  logic [7:0][31:0]     key_init[NumShares];
  logic [3:0][3:0][7:0] state_done[NumShares];
  logic [3:0][3:0][7:0] state_out;

  //--------------------------------------------
  // AES cipher core
  //--------------------------------------------

  assign state_init[0] = aes_pkg::aes_transpose({<<8{req_data_i.v}});
  assign key_init[0]   = {<<8{req_data_i.key}};

  assign state_out  = aes_pkg::aes_transpose(state_done[0]);
  assign rsp_data_o = {<<8{state_out}};

  assign cipher_in_valid = (enable_i && req_vld_i) ? aes_pkg::SP2V_HIGH : aes_pkg::SP2V_LOW;

  // SEC_CM: AES_CIPHER.FSM.SPARSE
  // SEC_CM: AES_CIPHER.FSM.REDUN
  // SEC_CM: AES_CIPHER.CTRL.SPARSE
  // SEC_CM: AES_CIPHER.FSM.LOCAL_ESC
  // SEC_CM: AES_CIPHER.CTR.REDUN
  // SEC_CM: AES_CIPHER.DATA_REG.LOCAL_ESC

  aes_cipher_core #(
    .AES192Enable (1'b0),  // AES192Enable disabled
    .CiphOpFwdOnly(1'b1),  // Forward operation only
    .SecMasking   (1'b0),  // Masking disable
    .SecSBoxImpl  (SBoxImpl)
  ) u_aes_cipher_core (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    .cfg_valid_i         (1'b1),
    .in_valid_i          (cipher_in_valid),
    .in_ready_o          (cipher_in_ready),
    .out_valid_o         (cipher_out_valid),
    .out_ready_i         (cipher_out_ready),
    .op_i                (aes_pkg::CIPH_FWD),
    .key_len_i           (aes_pkg::AES_256),
    .crypt_i             (aes_pkg::SP2V_HIGH), // Enable
    .crypt_o             (),
    .alert_fatal_i       (1'b0),
    .alert_o             (cipher_sm_err_o),
    .dec_key_gen_i       (aes_pkg::SP2V_LOW), // Disable
    .dec_key_gen_o       (),
    .prng_reseed_i       (1'b0), // Disable
    .prng_reseed_o       (),
    .key_clear_i         (1'b0), // Disable
    .key_clear_o         (),
    .data_out_clear_i    (1'b0), // Disable
    .data_out_clear_o    (),
    // These two init values are provided to allow synthesis to perform optimizations.
    // We don't care about SCA leakage in this context.
    .prd_clearing_state_i(state_init),
    .prd_clearing_key_i  (key_init),
    .force_masks_i       (1'b0),
    .data_in_mask_o      (),
    .entropy_req_o       (),
    .entropy_ack_i       (1'b0),
    .entropy_i           ('0),
    .state_init_i        (state_init),
    .key_init_i          (key_init),
    .state_o             (state_done)
  );

  // The cipher determines whether the response is ready for consumption
  assign rsp_vld_o = (cipher_out_valid == aes_pkg::SP2V_HIGH);

  // Type conversion for AES compatibility
  assign req_rdy_o = (cipher_in_ready == aes_pkg::SP2V_HIGH);
  assign cipher_out_ready = rsp_rdy_i ? aes_pkg::SP2V_HIGH : aes_pkg::SP2V_LOW;

endmodule
