// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package aes_model_dpi_pkg;
  import aes_pkg::*;

  // DPI-C imports
  import "DPI-C" context function void c_dpi_aes_crypt_block(
    input  bit                impl_i,    // 0 = C model, 1 = OpenSSL/BoringSSL
    input  bit                op_i,      // 0 = encrypt, 1 = decrypt
    input  bit          [5:0] mode_i,    // 6'b00_0001 = ECB, 6'00_b0010 = CBC, 6'b00_0100 = CFB,
                                         // 6'b00_1000 = OFB, 6'b01_0000 = CTR, 6'b10_0000 = NONE
    input  bit[3:0][3:0][7:0] iv_i,
    input  bit          [2:0] key_len_i, // 3'b001 = 128b, 3'b010 = 192b, 3'b100 = 256b
    input  bit    [7:0][31:0] key_i,
    input  bit[3:0][3:0][7:0] data_i,
    output bit[3:0][3:0][7:0] data_o
  );

  import "DPI-C" context function void c_dpi_aes_crypt_message(
    input  bit              impl_i,    // 0 = C model, 1 = OpenSSL/BoringSSL
    input  bit              op_i,      // 0 = encrypt, 1 = decrypt
    input  bit        [5:0] mode_i,    // 6'b00_0001 = ECB, 6'00_b0010 = CBC, 6'b00_0100 = CFB,
                                       // 6'b00_1000 = OFB, 6'b01_0000 = CTR, 6'b10_0000 = NONE
    input  bit  [3:0][31:0] iv_i,
    input  bit        [2:0] key_len_i, // 3'b001 = 128b, 3'b010 = 192b, 3'b100 = 256b
    input  bit  [7:0][31:0] key_i,
    input  bit        [7:0] data_i[],
    output bit        [7:0] data_o[]
  );

  import "DPI-C" context function void c_dpi_aes_sub_bytes(
    input  bit                op_i, // 0 = encrypt, 1 = decrypt
    input  bit[3:0][3:0][7:0] data_i,
    output bit[3:0][3:0][7:0] data_o
  );

  import "DPI-C" context function void c_dpi_aes_shift_rows(
    input  bit                op_i, // 0 = encrypt, 1 = decrypt
    input  bit[3:0][3:0][7:0] data_i,
    output bit[3:0][3:0][7:0] data_o
  );

  import "DPI-C" context function void c_dpi_aes_mix_columns(
    input  bit                op_i, // 0 = encrypt, 1 = decrypt
    input  bit[3:0][3:0][7:0] data_i,
    output bit[3:0][3:0][7:0] data_o
  );

  import "DPI-C" context function void c_dpi_aes_key_expand(
    input  bit            op_i,      // 0 = encrypt, 1 = decrypt
    input  bit      [7:0] rcon_i,
    input  bit      [3:0] round_i,
    input  bit      [2:0] key_len_i, // 3'b001 = 128b, 3'b010 = 192b, 3'b100 = 256b
    input  bit[7:0][31:0] key_i,
    output bit[7:0][31:0] key_o
  );

  // wrapper function that converts from register format (4x32bit)
  // to the 4x4x8 format of the c functions and back
  // this ensures that RTL and refence models have same input and output format.
  function automatic void sv_dpi_aes_crypt_block(
    input  bit             impl_i,    // 0 = C model, 1 = OpenSSL/BoringSSL
    input  bit             op_i,      // 0 = encrypt, 1 = decrypt
    input  bit       [5:0] mode_i,    // 6'b00_0001 = ECB, 6'00_b0010 = CBC, 6'b00_0100 = CFB,
                                      // 6'b00_1000 = OFB, 6'b01_0000 = CTR, 6'b10_0000 = NONE
    input  bit [3:0][31:0] iv_i,
    input  bit       [2:0] key_len_i, // 3'b001 = 128b, 3'b010 = 192b, 3'b100 = 256b
    input  bit [7:0][31:0] key_i,
    input  bit [3:0][31:0] data_i,
    output bit [3:0][31:0] data_o);

    bit [3:0][3:0][7:0] iv_in, data_in, data_out;
    data_in = aes_transpose(data_i);
    iv_in   = aes_transpose(iv_i);
    c_dpi_aes_crypt_block(impl_i, op_i, mode_i, iv_in, key_len_i, key_i, data_in, data_out);
    data_o  = aes_transpose(data_out);
    return;
  endfunction // sv_dpi_aes_crypt_block
endpackage
