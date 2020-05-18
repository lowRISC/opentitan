// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package crypto_dpi_present_pkg;

  // dep packages
  import uvm_pkg::*;

  // parameters

  // This is defined here so we can size all arrays properly.
  parameter int unsigned NumRounds = 31;

  // DPI-C imports
  import "DPI-C" context function void c_dpi_key_schedule(
    input longint unsigned  key_high,
    input longint unsigned  key_low,
    input int unsigned      num_rounds,
    input int unsigned      key_size_80,
    output bit [NumRounds:0][63:0] key_schedule
  );

  import "DPI-C" context function longint c_dpi_encrypt(
    input longint unsigned  plaintext,
    input longint unsigned  key_high,
    input longint unsigned  key_low,
    input int unsigned      num_rounds,
    input int unsigned      key_size_80
  );

  import "DPI-C" context function longint c_dpi_decrypt(
    input longint unsigned  ciphertext,
    input longint unsigned  key_high,
    input longint unsigned  key_low,
    input int unsigned      num_rounds,
    input int unsigned      key_size_80
  );

  // Helper Functions
  function automatic void get_keys(input bit [127:0] key,
                                   input bit         key_size_80,
                                   output bit [63:0] key_high,
                                   output bit [63:0] key_low);
    key_high = (key_size_80) ? key[79:16] : key[127:64];
    key_low = (key_size_80) ? key[15:0] : key[63:0];
  endfunction

  //////////////////////////////////////////////////////
  // SV wrapper functions to be used by the testbench //
  //////////////////////////////////////////////////////

  // This function takes in a 128 bit key by default, it determines how to
  // split this key for the DPI calls based on the value of key_size_80.
  //
  // This returns the list of round keys used during the course of the algorithm.
  function automatic void sv_dpi_present_get_key_schedule(
    input bit [127:0]                   key,
    input bit                           key_size_80,
    output bit [NumRounds:0][63:0]      key_schedule
  );
    bit [63:0] key_high, key_low;
    bit [(NumRounds*2)+1:0][31:0] compressed_key_schedule;

    get_keys(key, key_size_80, key_high, key_low);

    c_dpi_key_schedule(key_high, key_low, NumRounds+1, key_size_80, compressed_key_schedule);

    for (int i = 0; i < NumRounds+1; i++) begin
      key_schedule[i][31:0] = compressed_key_schedule[i*2];
      key_schedule[i][63:32] = compressed_key_schedule[i*2+1];
    end

  endfunction

  // This function encrypts the input plaintext with the PRESENT encryption
  // algorithm using the specified number of rounds.
  //
  // This produces a list of all intermediate values produced after each round
  // of the algorithm, including the final encrypted ciphertext value.
  function automatic void sv_dpi_present_encrypt(
    input bit [63:0]                  plaintext,
    input bit [127:0]                 key,
    input bit                         key_size_80,
    output bit [NumRounds-1:0][63:0]  encrypted_values
  );

    bit [63:0] key_high, key_low;

    get_keys(key, key_size_80, key_high, key_low);

    for (int i = 1; i <= NumRounds; i++) begin
      encrypted_values[i-1] = c_dpi_encrypt(plaintext, key_high, key_low, i+1, key_size_80);
    end

  endfunction

  // This function decrypts the input ciphertext with the PRESENT decryption
  // algorithm using the specified number of rounds.
  //
  // This produces a list of all intermediate values produced after each round
  // of the algorithm, including the final decrypted plaintext value.
  function automatic void sv_dpi_present_decrypt(
    input bit [NumRounds-1:0][63:0]   ciphertext,
    input bit [127:0]                 key,
    input bit                         key_size_80,
    output bit [NumRounds-1:0][63:0]  decrypted_values
  );

    bit [63:0] key_high, key_low;

    get_keys(key, key_size_80, key_high, key_low);

    for (int i = 1; i <= NumRounds; i++) begin
      decrypted_values[i-1] = c_dpi_decrypt(ciphertext[i-1], key_high, key_low, i+1, key_size_80);
    end

  endfunction

endpackage
