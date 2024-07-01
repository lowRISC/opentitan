// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package ascon_model_dpi_pkg;


  import "DPI-C" context function void c_dpi_ascon_round(
    input  bit[4:0][7:0][7:0] data_i,
    input  bit[7:0] round_i,
    output bit[4:0][7:0][7:0] data_o
  );


  import "DPI-C" context function void c_dpi_aead_encrypt(
    output byte unsigned ct[],
    input byte unsigned msg[],
    input int msg_len,
    input byte unsigned ad[],
    input int unsigned ad_len,
    input byte unsigned nonce[],
    input byte unsigned key[]
  );

  import "DPI-C" context function void c_dpi_aead_decrypt(
    input byte unsigned ct[],
    input int ct_len,
    output byte unsigned msg[],
    input byte unsigned ad[],
    input int unsigned ad_len,
    input byte unsigned nonce[],
    input byte unsigned key[]
  );

endpackage
