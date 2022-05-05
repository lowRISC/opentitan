// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Wrapper functions to write different partitions in flash.
// This file is included in `mem_bkdr_util.sv` as a continuation of `mem_bkdr_util` class.

localparam int unsigned FlashDataWidth = flash_phy_pkg::DataWidth;
localparam int unsigned FlashStagesPerCycle = FlashDataWidth / flash_phy_pkg::GfMultCycles;
localparam int unsigned FlashKeySize = flash_phy_pkg::KeySize;
localparam int unsigned FlashNumRoundsHalf = crypto_dpi_prince_pkg::NumRoundsHalf;
localparam int unsigned FlashAddrWidth = 16;

localparam bit[FlashDataWidth-1:0] IPoly = FlashDataWidth'(1'b1) << 15 |
                                           FlashDataWidth'(1'b1) << 9  |
                                           FlashDataWidth'(1'b1) << 7  |
                                           FlashDataWidth'(1'b1) << 4  |
                                           FlashDataWidth'(1'b1) << 3  |
                                           FlashDataWidth'(1'b1) << 0;

function bit [FlashDataWidth-1:0] flash_gf_mult2(bit [FlashDataWidth-1:0] operand);
  bit [FlashDataWidth-1:0] mult_out;

  mult_out = operand[FlashDataWidth-1] ? (operand << 1) ^ IPoly : (operand << 1);
  return mult_out;
endfunction

function bit [FlashStagesPerCycle-1:0][FlashDataWidth-1:0] flash_gen_matrix(
    bit [FlashDataWidth-1:0] seed, bit init);
  bit [FlashStagesPerCycle-1:0][FlashDataWidth-1:0] matrix_out;

  matrix_out[0] = init ? seed : flash_gf_mult2(seed);
  matrix_out[FlashStagesPerCycle-1:1] = '0;
  for (int i = 1; i < FlashStagesPerCycle; i++) begin
    matrix_out[i] = flash_gf_mult2(matrix_out[i-1]);
  end
  return matrix_out;
endfunction

function bit [FlashDataWidth-1:0] flash_galois_multiply(bit [FlashKeySize-1:0] addr_key,
                                                          bit [FlashAddrWidth-1:0] addr);
  bit [FlashStagesPerCycle-1:0][FlashDataWidth-1:0] matrix[2];
  bit [FlashDataWidth-1:0] product[2];
  bit [FlashDataWidth-1:0] add_vector;
  bit [FlashDataWidth-1:0] mult_out;

  // generate matrix.
  matrix[0] =
      flash_gen_matrix({addr_key[FlashKeySize-FlashAddrWidth-1:FlashKeySize-64], addr}, 1'b1);
  matrix[1] = flash_gen_matrix(matrix[0][FlashStagesPerCycle-1], 1'b0);
  // galois multiply.
  for (int j = 0; j < 2; j++) begin
    mult_out = '0;
    for (int i = 0; i < FlashStagesPerCycle; i++) begin
      add_vector = addr_key[(j*FlashStagesPerCycle)+i] ? matrix[j][i] : '0;
      mult_out   = mult_out ^ add_vector;
    end
    product[j] = mult_out;
  end
  product[1] = product[1] ^ product[0];
  return product[1];
endfunction

virtual function void flash_write_scrambled(
    bit [FlashDataWidth-1:0] data, bit [FlashAddrWidth-1:0] byte_addr,
    bit [FlashKeySize-1:0] flash_addr_key, bit [FlashKeySize-1:0] flash_data_key);
  bit [FlashAddrWidth-1:0] word_addr;
  bit [FlashDataWidth-1:0] mask;
  bit [FlashDataWidth-1:0] masked_data;
  bit [FlashNumRoundsHalf-1:0][FlashDataWidth-1:0] scrambled_data;
  bit [71:0] ecc_72;
  bit [75:0] ecc_76;

  word_addr = byte_addr >> addr_lsb;
  mask = flash_galois_multiply(flash_addr_key, word_addr);
  masked_data = data ^ mask;

  crypto_dpi_prince_pkg::sv_dpi_prince_encrypt(.plaintext(masked_data), .key(flash_data_key),
                                               .old_key_schedule(0), .ciphertext(scrambled_data));
  masked_data = scrambled_data[FlashNumRoundsHalf-1] ^ mask;
  // ecc functions used are hardcoded to a fixed sized.
  err_detection_scheme = EccHamming_72_64;
  ecc_72 = get_ecc_computed_data(data[63:0]);
  err_detection_scheme = EccHamming_76_68;
  ecc_76 = get_ecc_computed_data({ecc_72[67:64], masked_data[63:0]});
  write(byte_addr, ecc_76);
endfunction
