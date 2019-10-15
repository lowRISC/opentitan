// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package aes_model_dpi_pkg;

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

endpackage
