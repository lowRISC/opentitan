// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Specialization of the `mem_bkdr_util` class for RRAM memory

class rram_ctrl_bkdr_util extends mem_bkdr_util;

  localparam int unsigned RramDataWidth      = rram_ctrl_pkg::DataWidth;
  localparam int unsigned RramKeySize        = rram_ctrl_pkg::KeySize;
  localparam int unsigned RramAddrW          = rram_ctrl_pkg::AddrW;
  localparam int unsigned RramStagesPerCycle = RramDataWidth / rram_ctrl_pkg::GfMultCycles;
  localparam int unsigned RramNumRoundsHalf  = crypto_dpi_prince_pkg::NumRoundsHalf;
  localparam int unsigned RramDataByteWidth  = $clog2(RramDataWidth / 8);

  // A GF-multiplier stage matrix, as produced by rram_gen_matrix() and consumed by
  // rram_galois_multiply().
  typedef bit [RramStagesPerCycle-1:0][RramDataWidth-1:0] rram_gf_matrix_t;

  // Initialize the class instance.
  //
  // All arguments are forwarded unmodified to `mem_bkdr_util::new()`
  //
  //   name                    UVM object instance name.
  //   path                    Hierarchical HDL path to the memory.
  //   depth                   The number of memory rows.
  //   n_bits                  The total size of the memory in bits.
  //   err_detection_scheme    The error detection scheme implemented for the memory. This class
  //                           only supports `ErrDetectionNone` for now (checked below).
  //   row_adapter             Adapter to access the internal row of a memory, for integrators
  //                           with a custom memory architecture - not used.
  //   num_prince_rounds_half  The number of PRINCE half-rounds - not used
  //   extra_bits_per_subword  The width of any additional metadata that is not captured in the
  //                           secded package - not used.
  //   system_base_addr        Base address of the memory.
  function new(string name = "", string path, int unsigned depth,
               longint unsigned n_bits, err_detection_e err_detection_scheme,
               mem_bkdr_util_row_adapter row_adapter = null,
               int num_prince_rounds_half = 3,
               int extra_bits_per_subword = 0, int unsigned system_base_addr = 0);

    super.new(name, path, depth, n_bits, err_detection_scheme, row_adapter,
              num_prince_rounds_half, extra_bits_per_subword, system_base_addr);

    // No ECC for now. once added, the functions below need to be adjusted
    `DV_CHECK_EQ_FATAL(err_detection_scheme, mem_bkdr_util_pkg::ErrDetectionNone)

    // The GF multiplier decomposition below mirrors the `prim_gf_mult` hardware, which requires
    // the datapath width to divide evenly into the number of multiplier stages.
    `DV_CHECK_EQ_FATAL(RramDataWidth % rram_ctrl_pkg::GfMultCycles, 0,
                        "RramDataWidth must be a multiple of GfMultCycles")
    `DV_CHECK_EQ_FATAL(RramDataWidth % 8, 0, "RramDataWidth must be a multiple of bytes")
  endfunction

  // Randomize the memory
  virtual function void randomize_mem();
    `uvm_info(`gfn, "Randomizing rram mem contents", UVM_LOW)
    for (int i = 0; i < depth; i++) begin
      uvm_hdl_data_t data;
      `DV_CHECK_STD_RANDOMIZE_FATAL(data, "Randomization failed!", path)
      write(i * bytes_per_word, data);
    end
  endfunction

  // Return the operand multiplied by 2 in the finite Galois field (GF(2^n) modulo ScrambleIPoly)
  static function bit [RramDataWidth-1:0] rram_gf_mult2(bit [RramDataWidth-1:0] operand);
    bit [RramDataWidth-1:0] mult_out;

    mult_out = operand[RramDataWidth-1] ? (operand << 1) ^ rram_ctrl_pkg::ScrambleIPoly :
                                          (operand << 1);
    return mult_out;
  endfunction

  // Generate the per-stage GF-multiplier matrix consumed by rram_galois_multiply(), mirroring
  // `prim_gf_mult`'s `gen_matrix` step.
  // `seed` is the running GF value carried over from the previous cycle's last row; `init` is set
  // for the very first iteration, in which case `seed` is used directly as row 0 instead of first
  // being multiplied by x. Each subsequent row is the previous row multiplied by x (rram_gf_mult2).
  static function rram_gf_matrix_t rram_gen_matrix(bit [RramDataWidth-1:0] seed, bit init);
    rram_gf_matrix_t matrix_out;

    matrix_out[0] = init ? seed : rram_gf_mult2(seed);
    for (int i = 1; i < RramStagesPerCycle; i++) begin
      matrix_out[i] = rram_gf_mult2(matrix_out[i-1]);
    end
    return matrix_out;
  endfunction

  // Compute the tweak for the XEX cipher. Tweak = GfMult128(addr, addr_key)
  static function bit [RramDataWidth-1:0] rram_galois_multiply(bit [RramKeySize-1:0] addr_key,
                                                               bit [RramAddrW-1:0] addr);
    bit [RramDataWidth-1:0] total_product = '0;
    bit [RramDataWidth-1:0] next_seed;

    // Initial seed
    next_seed = {'0, addr};

    for (int j = 0; j < rram_ctrl_pkg::GfMultCycles; j++) begin
      rram_gf_matrix_t current_matrix;
      bit [RramDataWidth-1:0] mult_out = '0;

      // Generate matrix for this chunk
      // Use init = 1 for the very first chunk, init = 0 for subsequent ones
      current_matrix = rram_gen_matrix(next_seed, (j == 0));
      for (int i = 0; i < RramStagesPerCycle; i++) begin
        if (addr_key[(j * RramStagesPerCycle) + i]) begin
          mult_out = mult_out ^ current_matrix[i];
        end
      end
      // Accumulate result
      total_product = total_product ^ mult_out;
      // Prepare seed for next loop: the last row of current matrix
      next_seed = current_matrix[RramStagesPerCycle-1];
    end

    return total_product;
  endfunction

  // Scramble a single RRAM word using the XEX cipher:
  // 1. Compute the tweak (gfmult128(addr_key, addr))
  // 2. Apply the tweak
  // 3. Encrypt the data with the data_key
  // 4. Remove the tweak
  function bit [RramDataWidth-1:0] rram_scramble_data(bit [RramDataWidth-1:0] data,
                                                      bit [RramAddrW-1:0] word_addr,
                                                      bit [RramKeySize-1:0] rram_addr_key,
                                                      bit [RramKeySize-1:0] rram_data_key);
    bit [RramDataWidth-1:0] masked_data;
    bit [RramDataWidth-1:0] scrambled_data;
    bit [RramDataWidth-1:0] mask;

    mask = rram_galois_multiply(rram_addr_key, word_addr);
    masked_data = data ^ mask;

    for (int k = 0; k < 2; k++) begin
      bit [RramDataWidth/2-1:0]                        cipher_in;
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

  // Descramble a single RRAM word using the XEX cipher:
  // 1. Compute the tweak (gfmult128(addr_key, addr))
  // 2. Apply the tweak
  // 3. Decrypt the data with the data_key
  // 4. Remove the tweak
  function bit [RramDataWidth-1:0] rram_descramble_data(bit [RramDataWidth-1:0] data,
                                                        bit [RramAddrW-1:0] word_addr,
                                                        bit [RramKeySize-1:0] rram_addr_key,
                                                        bit [RramKeySize-1:0] rram_data_key);
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

endclass
