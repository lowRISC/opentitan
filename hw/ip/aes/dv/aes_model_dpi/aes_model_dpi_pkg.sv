// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package aes_model_dpi_pkg;
  import aes_pkg::*;

  // DPI-C imports
  import "DPI-C" context function void aes_crypt_dpi(
    input  bit                impl_i,
    input  bit                mode_i,
    input  bit          [2:0] key_len_i,
    input  bit    [7:0][31:0] key_i,
    input  bit[3:0][3:0][7:0] data_i,
    output bit[3:0][3:0][7:0] data_o
  );

  import "DPI-C" context function void aes_sub_bytes_dpi(
    input  bit                mode_i,
    input  bit[3:0][3:0][7:0] data_i,
    output bit[3:0][3:0][7:0] data_o
  );

  import "DPI-C" context function void aes_shift_rows_dpi(
    input  bit                mode_i,
    input  bit[3:0][3:0][7:0] data_i,
    output bit[3:0][3:0][7:0] data_o
  );

  import "DPI-C" context function void aes_mix_columns_dpi(
    input  bit                mode_i,
    input  bit[3:0][3:0][7:0] data_i,
    output bit[3:0][3:0][7:0] data_o
  );

  import "DPI-C" context function void aes_key_expand_dpi(
    input  bit            mode_i,
    input  bit      [7:0] rcon_i,
    input  bit      [3:0] round_i,
    input  bit      [2:0] key_len_i,
    input  bit[7:0][31:0] key_i,
    output bit[7:0][31:0] key_o
  );

  // wrapper function that converts from register format (4x32bit)
  // to the 4x4x8 format of the c functions and back
  // this ensures that RTL and refence models have same input and output format.
  function automatic void aes_crypt(
    input  bit             impl_i,
    input  bit             mode_i,
    input  bit       [2:0] key_len_i,
    input  bit [7:0][31:0] key_i,
    input  bit [3:0][31:0] data_i,
    output bit [3:0][31:0] data_o);

    bit [3:0][3:0][7:0] data_in, data_out;
    data_in = aes_transpose(data_i);
    aes_crypt_dpi(impl_i, mode_i, key_len_i, key_i, data_in, data_out);
    data_o  = aes_transpose(data_out);
    return;
  endfunction

endpackage
