// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/////////////////////////////////////////////////
// OTP secret data and digest scrambling logic //
/////////////////////////////////////////////////

package otp_scrambler_pkg;

  import uvm_pkg::*;
  import otp_ctrl_reg_pkg::*;
  import otp_ctrl_part_pkg::*;
  import bus_params_pkg::*;

  `include "uvm_macros.svh"

  parameter int SCRAMBLE_DATA_SIZE = 64;
  parameter int SCRAMBLE_KEY_SIZE  = 128;
  parameter int NUM_ROUND          = 31;
  string path = "otp_scrambler_pkg";

  // When secret data write into otp_array, it will be scrambled.
  function automatic bit [SCRAMBLE_DATA_SIZE-1:0] scramble_data(
    bit [SCRAMBLE_DATA_SIZE-1:0] input_data,
    int part_idx
  );

    int secret_idx = part_idx - Secret0Idx;
    bit [NUM_ROUND-1:0][SCRAMBLE_DATA_SIZE-1:0] output_data;
    crypto_dpi_present_pkg::sv_dpi_present_encrypt(input_data,
                                                   RndCnstKey[secret_idx],
                                                   SCRAMBLE_KEY_SIZE == 80,
                                                   output_data);
    scramble_data = output_data[NUM_ROUND-1];
  endfunction

  // When secret data read out of otp_array, it will be descrambled.
  function automatic bit [SCRAMBLE_DATA_SIZE-1:0] descramble_data(
    bit [SCRAMBLE_DATA_SIZE-1:0] input_data,
    int part_idx
  );

    int secret_idx = part_idx - Secret0Idx;
    bit [NUM_ROUND-1:0][SCRAMBLE_DATA_SIZE-1:0] output_data;
    bit [NUM_ROUND-1:0][SCRAMBLE_DATA_SIZE-1:0] padded_input;

    padded_input[NUM_ROUND-1] = input_data;
    crypto_dpi_present_pkg::sv_dpi_present_decrypt(padded_input,
                                                   RndCnstKey[secret_idx],
                                                   SCRAMBLE_KEY_SIZE == 80,
                                                   output_data);
    descramble_data = output_data[NUM_ROUND-1];
    if (input_data != 0) begin
    end
  endfunction

  function automatic bit [SCRAMBLE_DATA_SIZE-1:0] cal_digest(int part_idx,
                                                             ref bit [BUS_DW-1:0] mem_q[$]);
    int array_size = mem_q.size();
    real key_factor  = SCRAMBLE_KEY_SIZE / BUS_DW;
    bit [NUM_ROUND-1:0] [SCRAMBLE_DATA_SIZE-1:0] enc_array;
    bit [SCRAMBLE_DATA_SIZE-1:0] init_vec = RndCnstDigestIV[0];
    bit [SCRAMBLE_DATA_SIZE-1:0] digest;

    for (int i = 0; i < $ceil(array_size / key_factor); i++) begin
      bit [SCRAMBLE_DATA_SIZE-1:0] input_data = (i == 0) ? init_vec : digest;
      bit [SCRAMBLE_KEY_SIZE-1:0]  key;

      // Pad 32-bit partition data into 128-bit key input.
      // Because the mem_q size is a multiple of 64-bit, so if the last round only has 64-bits key,
      // it will repeat the last 64-bits twice.
      for (int j = 0; j < key_factor; j++) begin
        int index = i * key_factor + j;
        key |= ((index >= array_size ? mem_q[index-2] : mem_q[index]) << (j * BUS_DW));
      end

      // Trigger 32 round of PRESENT encrypt.
      crypto_dpi_present_pkg::sv_dpi_present_encrypt(input_data, key, SCRAMBLE_KEY_SIZE == 80,
                                                     enc_array);
      // XOR the previous state into the digest result according to the Davies-Meyer scheme.
      digest = enc_array[NUM_ROUND-1] ^ input_data;
    end

    // Last 32 round of digest is calculated with a digest constant.
    crypto_dpi_present_pkg::sv_dpi_present_encrypt(digest,
                                                   RndCnstDigestConst[0],
                                                   SCRAMBLE_KEY_SIZE == 80,
                                                   enc_array);
    // XOR the previous state into the digest result according to the Davies-Meyer scheme.
    digest ^= enc_array[NUM_ROUND-1];
    return digest;
  endfunction

endpackage
