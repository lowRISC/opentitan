// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package crypto_dpi_present_pkg;
  // PRESENT expects up to 31 rounds in total
  localparam int unsigned MaxRounds = 31;
  localparam int unsigned MaxKeyWidth = 128;
  localparam int unsigned DataWidth = 64;

  // DPI-C imports
  import "DPI-C" function chandle c_dpi_present_mk(int unsigned          key_size,
                                                   bit [MaxKeyWidth-1:0] key);
  import "DPI-C" function void c_dpi_present_free(chandle h);

  import "DPI-C" function void c_dpi_present_enc_round(chandle                    h,
                                                       int unsigned               round,
                                                       bit                        is_last_round,
                                                       bit [DataWidth-1:0]        in,
                                                       output bit [DataWidth-1:0] out);
  import "DPI-C" function void c_dpi_present_dec_round(chandle                    h,
                                                       int unsigned               round,
                                                       bit                        is_last_round,
                                                       bit [DataWidth-1:0]        in,
                                                       output bit [DataWidth-1:0] out);

  // This function encrypts the input plaintext with the PRESENT encryption algorithm.
  //
  // This produces a list of all intermediate values produced after each round of the algorithm,
  // including the final encrypted ciphertext value.
  function automatic void sv_dpi_present_encrypt(
    input bit [DataWidth-1:0]   plaintext,
    input bit [MaxKeyWidth-1:0] key,
    input int unsigned          key_size,
    input int unsigned          num_rounds,
    output bit [DataWidth-1:0]  ciphertext
  );

    bit [DataWidth-1:0] round_in, round_out;
    chandle h = c_dpi_present_mk(key_size, key);

    round_out = plaintext;
    for (int i = 1; i <= num_rounds; i++) begin
      round_in = round_out;
      c_dpi_present_enc_round(h, i, i == num_rounds, round_in, round_out);
    end
    ciphertext = round_out;

    c_dpi_present_free(h);

  endfunction

  // This function decrypts the input ciphertext with the PRESENT decryption algorithm.
  //
  // This produces a list of all intermediate values produced after each round of the algorithm,
  // including the final decrypted plaintext value.
  function automatic void sv_dpi_present_decrypt(
    input bit [DataWidth-1:0]   ciphertext,
    input bit [MaxKeyWidth-1:0] key,
    input int unsigned          key_size,
    input int unsigned          num_rounds,
    output bit [DataWidth-1:0]  plaintext
  );

    bit [DataWidth-1:0] round_in, round_out;
    chandle h = c_dpi_present_mk(key_size, key);

    round_in = ciphertext;
    for (int i = num_rounds; i > 0; i--) begin
      c_dpi_present_dec_round(h, i, i == num_rounds, round_in, round_out);
      round_in = round_out;
    end
    plaintext = round_out;

    c_dpi_present_free(h);

  endfunction

endpackage
