// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Specialization of the `mem_bkdr_util` class for RRAM memory

class rram_ctrl_bkdr_util extends mem_bkdr_util;

  localparam int unsigned RramDataWidth = rram_ctrl_pkg::DataWidth;
  localparam int unsigned RramKeySize = rram_ctrl_pkg::KeySize;
  localparam int unsigned RramAddrW = rram_ctrl_pkg::AddrW;
  localparam int unsigned RramStagesPerCycle = RramDataWidth / rram_ctrl_pkg::GfMultCycles;
  localparam int unsigned RramNumRoundsHalf = crypto_dpi_prince_pkg::NumRoundsHalf;

  localparam int unsigned RramDataByteWidth = $clog2(RramDataWidth / 8);

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
    // No ECC for now. once added, the functions below need to be adjusted
    `DV_CHECK_EQ_FATAL(err_detection_scheme, mem_bkdr_util_pkg::ErrDetectionNone)
  endfunction

  // Randomize the memory with correct ECC.
  virtual function void randomize_mem();
    `uvm_info(`gfn, "Randomizing rram mem contents", UVM_LOW)
    for (int i = 0; i < depth; i++) begin
      uvm_hdl_data_t data;
      `DV_CHECK_STD_RANDOMIZE_FATAL(data, "Randomization failed!", path)
      write(i * bytes_per_word, data);
    end
  endfunction

  static function bit [RramDataWidth-1:0] rram_gf_mult2(bit [RramDataWidth-1:0] operand);
    bit [RramDataWidth-1:0] mult_out;

    mult_out = operand[RramDataWidth-1] ? (operand << 1) ^
     rram_ctrl_pkg::ScrambleIPoly : (operand << 1);
    return mult_out;
  endfunction

  static function bit [RramStagesPerCycle-1:0][RramDataWidth-1:0] rram_gen_matrix(
      bit [RramDataWidth-1:0] seed, bit init);
    bit [RramStagesPerCycle-1:0][RramDataWidth-1:0] matrix_out;

    matrix_out[0] = init ? seed : rram_gf_mult2(seed);
    matrix_out[RramStagesPerCycle-1:1] = '0;
    for (int i = 1; i < RramStagesPerCycle; i++) begin
      matrix_out[i] = rram_gf_mult2(matrix_out[i-1]);
    end
    return matrix_out;
  endfunction

  static function bit [RramDataWidth-1:0] rram_galois_multiply(bit [RramKeySize-1:0] addr_key,
                                                    bit [RramAddrW-1:0] addr);
    bit [RramStagesPerCycle-1:0][RramDataWidth-1:0] matrix[2];
    bit [RramDataWidth-1:0] product[2];
    bit [RramDataWidth-1:0] add_vector;
    bit [RramDataWidth-1:0] mult_out;

    // generate matrix.
    matrix[0] =
        rram_gen_matrix({addr_key[RramKeySize-1:RramAddrW], addr}, 1'b1);
    matrix[1] = rram_gen_matrix(matrix[0][RramStagesPerCycle-1], 1'b0);
    // galois multiply.
    for (int j = 0; j < 2; j++) begin
      mult_out = '0;
      for (int i = 0; i < RramStagesPerCycle; i++) begin
        add_vector = addr_key[(j*RramStagesPerCycle)+i] ? matrix[j][i] : '0;
        mult_out   = mult_out ^ add_vector;
      end
      product[j] = mult_out;
    end
    product[1] = product[1] ^ product[0];
    return product[1];
  endfunction

  function bit [RramDataWidth-1:0] rram_scramble_data(
      bit [RramDataWidth-1:0] data, bit [RramAddrW-1:0] word_addr,
      bit [RramKeySize-1:0] rram_addr_key, bit [RramKeySize-1:0] rram_data_key);
    bit [RramDataWidth-1:0] masked_data;
    bit [RramDataWidth-1:0] scrambled_data;
    bit [RramDataWidth-1:0] mask;

    mask = rram_galois_multiply(rram_addr_key, word_addr);
    masked_data = data ^ mask;

    for (int k = 0; k < 2; k++) begin
      bit [RramDataWidth/2-1:0] cipher_in;
      bit [RramNumRoundsHalf-1:0][RramDataWidth/2-1:0] cipher_out;
      for (int i = 0; i < RramDataWidth/2; i++) begin
        cipher_in[i] = masked_data[2*i+k];
      end
      crypto_dpi_prince_pkg::sv_dpi_prince_encrypt(.plaintext(cipher_in),
                                                   .key(rram_data_key),
                                                   .old_key_schedule(0),
                                                   .ciphertext(cipher_out));
      for (int i = 0; i < RramDataWidth/2; i++) begin
        scrambled_data[2*i+k] = cipher_out[RramNumRoundsHalf-1][i];
      end
    end
    return scrambled_data ^ mask;
  endfunction

  function bit [RramDataWidth-1:0] rram_descramble_data(
      bit [RramDataWidth-1:0] data, bit [RramAddrW-1:0] word_addr,
      bit [RramKeySize-1:0] rram_addr_key, bit [RramKeySize-1:0] rram_data_key);
    bit [RramDataWidth-1:0] masked_data;
    bit [RramDataWidth-1:0] descrambled_data;
    bit [RramDataWidth-1:0] mask;

    mask = rram_galois_multiply(rram_addr_key, word_addr);
    masked_data = data ^ mask;

    for (int k = 0; k < 2; k++) begin
      bit [RramDataWidth/2-1:0] cipher_in;
      bit [RramDataWidth/2-1:0] cipher_out;
      for (int i = 0; i < RramDataWidth/2; i++) begin
        cipher_in[i] = masked_data[2*i+k];
      end
      cipher_out = crypto_dpi_prince_pkg::c_dpi_prince_decrypt(cipher_in,
                                                     rram_data_key[127:64],
                                                     rram_data_key[63:0],
                                                     RramNumRoundsHalf,
                                                     0);
      for (int i = 0; i < RramDataWidth/2; i++) begin
        descrambled_data[2*i+k] = cipher_out[i];
      end
    end

    return descrambled_data ^ mask;
  endfunction

  virtual function void rram_write_scrambled(
      bit [RramDataWidth-1:0] data, bit [RramAddrW-1:0] word_addr,
      bit [RramKeySize-1:0] rram_addr_key, bit [RramKeySize-1:0] rram_data_key);
    bit [RramDataWidth-1:0] scrambled_data;
    bit [rram_ctrl_pkg::BusAddrByteW-1:0] byte_addr;

    scrambled_data = rram_scramble_data(data, word_addr, rram_addr_key, rram_data_key);

    // ecc is not yet implemented

    byte_addr = word_addr << RramDataByteWidth;
    write(byte_addr, scrambled_data);
  endfunction

  virtual function void rram_read_scrambled(
      ref bit [RramDataWidth-1:0] data, bit [RramAddrW-1:0] word_addr,
      bit [RramKeySize-1:0] rram_addr_key, bit [RramKeySize-1:0] rram_data_key);
    bit [RramDataWidth-1:0] scrambled_data;
    bit [rram_ctrl_pkg::BusAddrByteW-1:0] byte_addr;

    byte_addr = word_addr << RramDataByteWidth;
    scrambled_data = read(byte_addr);

    // ecc is not yet implemented

    data = rram_descramble_data(scrambled_data, word_addr, rram_addr_key, rram_data_key);

  endfunction

endclass
