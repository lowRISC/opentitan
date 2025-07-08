// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Specialization of the `mem_bkdr_util` class for flash memories.

class flash_ctrl_bkdr_util extends mem_bkdr_util;

  localparam int unsigned FlashDataWidth = flash_phy_pkg::DataWidth;
  localparam int unsigned FlashStagesPerCycle = FlashDataWidth / flash_phy_pkg::GfMultCycles;
  localparam int unsigned FlashKeySize = flash_phy_pkg::KeySize;
  localparam int unsigned FlashNumRoundsHalf = crypto_dpi_prince_pkg::NumRoundsHalf;
  localparam int unsigned FlashAddrWidth = 16;

  localparam int unsigned FlashBankBytesPerWord = FlashDataWidth / 8;

  localparam int unsigned FlashDataByteWidth = $clog2(FlashBankBytesPerWord);

  // Initialize the class instance.
  // `extra_bits_per_subword` is the width of any additional metadata that is not captured in the
  // secded package.
  function new(string name = "", string path, int unsigned depth,
               longint unsigned n_bits, err_detection_e err_detection_scheme,
               mem_bkdr_util_row_adapter row_adapter = null,
               int num_prince_rounds_half = 3,
               int extra_bits_per_subword = 0, int unsigned system_base_addr = 0);
    super.new(name, path, depth, n_bits, err_detection_scheme, row_adapter, num_prince_rounds_half,
              extra_bits_per_subword, system_base_addr);
    // Error detection scheme is assumed to be 76_68, otherwise, the overrides below won't work.
    `DV_CHECK_EQ_FATAL(err_detection_scheme, mem_bkdr_util_pkg::EccHamming_76_68)
  endfunction

  // Flash has 2 levels of ECC - first on bits 63:0 applied to bits 71:64.
  virtual function uvm_hdl_data_t get_ecc_computed_data(uvm_hdl_data_t data);
    data = prim_secded_pkg::prim_secded_hamming_72_64_enc(data[63:0]);
    return super.get_ecc_computed_data(data);
  endfunction

  // Randomize the memory with correct ECC.
  virtual function void randomize_mem();
    `uvm_info(`gfn, "Randomizing flash mem contents", UVM_LOW)
    for (int i = 0; i < depth; i++) begin
      uvm_hdl_data_t data;
      `DV_CHECK_STD_RANDOMIZE_FATAL(data, "Randomization failed!", path)
      data = prim_secded_pkg::prim_secded_hamming_72_64_enc(data[63:0]);
      data = get_ecc_computed_data(data);
      write(i * bytes_per_word, data);
    end
  endfunction

  static function bit [FlashDataWidth-1:0] flash_gf_mult2(bit [FlashDataWidth-1:0] operand);
    bit [FlashDataWidth-1:0] mult_out;

    mult_out = operand[FlashDataWidth-1] ? (operand << 1) ^
      flash_phy_pkg::ScrambleIPoly : (operand << 1);
    return mult_out;
  endfunction

  static function bit [FlashStagesPerCycle-1:0][FlashDataWidth-1:0] flash_gen_matrix(
      bit [FlashDataWidth-1:0] seed, bit init);
    bit [FlashStagesPerCycle-1:0][FlashDataWidth-1:0] matrix_out;

    matrix_out[0] = init ? seed : flash_gf_mult2(seed);
    matrix_out[FlashStagesPerCycle-1:1] = '0;
    for (int i = 1; i < FlashStagesPerCycle; i++) begin
      matrix_out[i] = flash_gf_mult2(matrix_out[i-1]);
    end
    return matrix_out;
  endfunction

  static function bit [FlashDataWidth-1:0] flash_galois_multiply(bit [FlashKeySize-1:0] addr_key,
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

  // TODO; consider changing these functions to member functions and retaining the flash_addr_
  // and flash_data_ keys as members.
  static function bit [FlashDataWidth-1:0] flash_create_masked_data(
      bit [FlashDataWidth-1:0] data, bit [FlashAddrWidth-1:0] byte_addr,
      bit [FlashKeySize-1:0] flash_addr_key, bit [FlashKeySize-1:0] flash_data_key);
    bit [FlashNumRoundsHalf-1:0][FlashDataWidth-1:0] scrambled_data;
    bit [FlashDataWidth-1:0] masked_data;
    bit [FlashDataWidth-1:0] mask;

    mask = flash_galois_multiply(flash_addr_key, byte_addr >> FlashDataByteWidth);
    masked_data = data ^ mask;

    crypto_dpi_prince_pkg::sv_dpi_prince_encrypt(.plaintext(masked_data), .key(flash_data_key),
                                                 .old_key_schedule(0), .ciphertext(scrambled_data));
    return scrambled_data[FlashNumRoundsHalf-1] ^ mask;
  endfunction

  virtual function void flash_write_scrambled(
      bit [FlashDataWidth-1:0] data, bit [FlashAddrWidth-1:0] byte_addr,
      bit [FlashKeySize-1:0] flash_addr_key, bit [FlashKeySize-1:0] flash_data_key);
    bit [FlashDataWidth-1:0] masked_data;
    bit [71:0] ecc_72;
    bit [75:0] ecc_76;

    masked_data = flash_create_masked_data(data, byte_addr, flash_addr_key, flash_data_key);

    // ecc functions used are hardcoded to a fixed sized.
    ecc_72 = prim_secded_pkg::prim_secded_hamming_72_64_enc(data[63:0]);
    ecc_76 = prim_secded_pkg::prim_secded_hamming_76_68_enc({ecc_72[67:64], masked_data[63:0]});
    write(byte_addr, ecc_76);
  endfunction
endclass
