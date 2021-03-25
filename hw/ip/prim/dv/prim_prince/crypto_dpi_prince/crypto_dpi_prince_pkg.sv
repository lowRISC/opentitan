// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package crypto_dpi_prince_pkg;

  // dep packages

  // parameters
  // Max number of half-rounds.
  parameter int unsigned NumRoundsHalf = 5;

  // DPI-C imports
  import "DPI-C" context function longint c_dpi_prince_encrypt(
    input longint unsigned  data,
    input longint unsigned  key0,
    input longint unsigned  key1,
    input int unsigned      num_half_rounds,
    input int unsigned      new_key_schedule
  );

  import "DPI-C" context function longint c_dpi_prince_decrypt(
    input longint unsigned  data,
    input longint unsigned  key0,
    input longint unsigned  key1,
    input int unsigned      num_half_rounds,
    input int unsigned      new_key_schedule
  );

  //////////////////////////////////////////////////////
  // SV wrapper functions to be used by the testbench //
  //////////////////////////////////////////////////////

  function automatic void sv_dpi_prince_encrypt(
    input bit [63:0]                      plaintext,
    input bit [127:0]                     key,
    input bit                             old_key_schedule,
    output bit [NumRoundsHalf-1:0][63:0]  ciphertext
  );
    for (int i = 0; i < NumRoundsHalf; i++) begin
      ciphertext[i] = c_dpi_prince_encrypt(plaintext,
                                           key[127:64], // k0 gets assigned the MSB halve
                                           key[63:0],   // k1 gets assigned the LSB halve
                                           i+1,
                                           old_key_schedule);
    end
  endfunction

  function automatic void sv_dpi_prince_decrypt(
    input bit [NumRoundsHalf-1:0][63:0]   ciphertext,
    input bit [127:0]                     key,
    input bit                             old_key_schedule,
    output bit [NumRoundsHalf-1:0][63:0]  plaintext
  );
    for (int i = 0; i < NumRoundsHalf; i++) begin
      plaintext[i] = c_dpi_prince_decrypt(ciphertext[i],
                                          key[127:64],  // k0 gets assigned the MSB halve
                                          key[63:0],    // k1 gets assigned the LSB halve
                                          i+1,
                                          old_key_schedule);
    end
  endfunction

endpackage
