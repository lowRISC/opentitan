// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

////////////////////////////////////////////
// SRAM address and data scrambling logic //
///////////////////////////////////////////
//
// There are a few general things to note here:
//
// - SRAM data scrambling relies on a reduced-round PRINCE cipher, plus a custom substitution
//   and permutation network loosely based off of PRESENT.
//
// - SRAM address scrambling relies solely on the custom substitution and permutation network.
//
// - The custom subst/perm network used for data scrambling operates at byte granularity,
//   while for address scrambling it operates at a granularity of the address width.
//
// - For DV purposes we can safely rely on the PRESENT sboxes, as nightly regressions are
//   completely passing plus the sboxes in `prim_cipher_pkg` are copied directly from the
//   PRESENT specifications.
//   This has the side effect of allowing us to avoid duplication of the sboxes, which lowers the
//   probability of an error in translation.

package sram_scrambler_pkg;

  import uvm_pkg::*;
  import bus_params_pkg::BUS_AW;
  import crypto_dpi_prince_pkg::*;
  import prim_cipher_pkg::*;

  `include "uvm_macros.svh"

  string path = "sram_scrambler_pkg";

  // Fixed key size - PRINCE cipher operates on a 128-bit key,
  // and the same key is used for all parallel cipher instances.
  parameter int SRAM_KEY_WIDTH = 128;

  // Fixed data block size - PRINCE cipher operates on 64-bit data blocks.
  parameter int SRAM_BLOCK_WIDTH = 64;

  parameter int NUM_ROUNDS = 2;

  // Create a generic typedef for dynamic array of logic to be able to return these values.
  typedef logic state_t[];

  // The sboxes operate on nibbles.
  //
  // If `WIDTH % 4 != 0`, the uppermost bits will get shifted to lower positions
  // during either the `flip_vector` or `perm_layer` stage of the network,
  // so it is guaranted that all bits will eventually go through an sbox.
  function automatic state_t sbox_layer(state_t state, int width, bit inv);
    logic state_out[] = new[width](state);
    logic [3:0] sbox_in;
    logic [3:0] sbox_out;
    for (int i = 0; i < width / 4; i++) begin
      // `with` syntax is currently unsupported by Verible,
      // uncomment once support has been added
      //
      //sbox_in = {<< {state with [i*4 +: 4]}};
      for (int j = 0; j < 4; j++) begin
        sbox_in[j] = state[i*4 + j];
      end

      if (inv) begin
        sbox_out = prim_cipher_pkg::PRESENT_SBOX4_INV[sbox_in];
      end else begin
        sbox_out = prim_cipher_pkg::PRESENT_SBOX4[sbox_in];
      end

      for (int j = 0; j < 4; j++) begin
        state_out[i*4 + j] = sbox_out[j];
      end
    end
    return state_out;
  endfunction : sbox_layer

  // Reverse the input bit vector.
  function automatic state_t flip_vector(state_t state);
    return {<< {state}};
  endfunction : flip_vector

  // Permutation layer - all even indexed bits move to the lower half,
  // and all odd indexed bits move to the top half.
  function automatic state_t perm_layer(state_t state, int width, bit inv);
    logic state_out[] = new[width](state);
    for (int i = 0; i < width / 2; i++) begin
      if (inv) begin
        state_out[i * 2]          = state[i];
        state_out[i * 2 + 1]      = state[i + width / 2];
      end else begin
        state_out[i]              = state[i * 2];
        state_out[i + width / 2]  = state[i * 2 + 1];
      end
    end
    return state_out;
  endfunction : perm_layer

  // Performs NUM_ROUNDS full encryption rounds
  function automatic state_t sp_encrypt(state_t data, int width, state_t key);
    logic state[] = new[width](data);
    for (int i = 0; i < NUM_ROUNDS; i++) begin
      // xor the data and key
      for (int j = 0; j < width; j++) begin
        state[j] = state[j] ^ key[j];
      end
      // sbox layer
      state = sbox_layer(state, width, 0);
      // flip the bit vector
      state = flip_vector(state);
      // permutation layer
      state = perm_layer(state, width, 0);
    end
    // final xor
    for (int i = 0; i < width; i++) begin
      state[i] = state[i] ^ key[i];
    end
    return state;
  endfunction : sp_encrypt

  // Performs NUM_ROUNDS full decryption rounds
  function automatic state_t sp_decrypt(state_t data, int width, state_t key);
    logic state[] = new[width](data);
    for (int i = 0; i < NUM_ROUNDS; i++) begin
      // xor data and key
      for (int j = 0; j < width; j++) begin
        state[j] = state[j] ^ key[j];
      end
      // permutation layer
      state = perm_layer(state, width, 1);
      // flip bit vector
      state = flip_vector(state);
      // sbox layer
      state = sbox_layer(state, width, 1'b1);
    end
    // final xor
    for (int i = 0; i < width; i++) begin
      state[i] = state[i] ^ key[i];
    end
    return state;
  endfunction : sp_decrypt

  // Generates the 64-bit keystream that is XORed with the data to obtain a ciphertext.
  // Assumes that the data is at most 64 bits wide.
  //
  // Should not be called directly.
  function automatic state_t gen_keystream(logic addr[], int addr_width,
                                           logic key[], logic nonce[]);
    logic [NUM_ROUNDS-1:0][SRAM_BLOCK_WIDTH-1:0] prince_result_arr;

    logic [SRAM_BLOCK_WIDTH-1:0]  prince_plaintext;
    logic [SRAM_KEY_WIDTH-1:0]    prince_key;
    logic [SRAM_BLOCK_WIDTH-1:0]  prince_result;

    logic iv[]      = new[SRAM_BLOCK_WIDTH];
    logic key_out[] = new[SRAM_BLOCK_WIDTH];

    // IV is composed of nonce concatenated with address
    for (int i = 0; i < addr_width; i++) begin
      iv[i] = addr[i];
    end
    for (int i = 0; i < SRAM_BLOCK_WIDTH - addr_width; i++) begin
      iv[addr_width + i] = nonce[i];
    end

    //for (int i = 0; i < SRAM_BLOCK_WIDTH - addr_width; i++) begin
    //  iv[addr_width + i] = nonce[i];
    //end

    // convert arrays to packed vectors before invoking prince DPI model
    prince_plaintext = {<< {iv}};
    // `with` syntax is currently unsupported by Verible,
    // uncomment once support has been added
    //
    // prince_key = {<< {key with [0 +: SRAM_KEY_WIDTH]}};
    for (int i = 0; i < SRAM_KEY_WIDTH; i++) begin
      prince_key[i] = key[i];
    end

    crypto_dpi_prince_pkg::sv_dpi_prince_encrypt(.plaintext(prince_plaintext),
                                                 .key(prince_key),
                                                 .old_key_schedule(0),
                                                 .ciphertext(prince_result_arr));
    prince_result = prince_result_arr[NUM_ROUNDS-1];

    key_out = {<< {prince_result}};

    return key_out;
  endfunction : gen_keystream

  // Encrypts the target SRAM address using the custom S&P network.
  function automatic state_t encrypt_sram_addr(logic addr[], int addr_width,
                                               logic full_nonce[]);

    logic nonce[] = new[addr_width];
    logic encrypted_addr[] = new[addr_width];

    // The address encryption nonce is the same width as the address,
    // and is constructed from the top addr_width bits of the full nonce.
    //
    // `with` syntax is currently unsupported by Verible,
    // uncomment once support has been added
    //
    // nonce = {>> {full_nonce with [SRAM_BLOCK_WIDTH - addr_width +: addr_width]}};
    for (int i = 0; i < addr_width; i++) begin
      nonce[i] = full_nonce[SRAM_BLOCK_WIDTH - addr_width + i];
    end
    encrypted_addr = sp_encrypt(addr, addr_width, nonce);
    return encrypted_addr;

  endfunction : encrypt_sram_addr

  // Deccrypts the target SRAM address using the custom S&P network.
  function automatic state_t decrypt_sram_addr(logic addr[], int addr_width,
                                               logic full_nonce[]);

    logic nonce[] = new[addr_width];
    logic encrypted_addr[] = new[addr_width];

    // The address encryption nonce is the same width as the address,
    // and is constructed from the top addr_width bits of the full nonce.
    //
    // `with` syntax is currently unsupported by Verible,
    // uncomment once support has been added
    //
    // nonce = {>> {full_nonce with [SRAM_BLOCK_WIDTH - addr_width +: addr_width]}};
    for (int i = 0; i < addr_width; i++) begin
      nonce[i] = full_nonce[SRAM_BLOCK_WIDTH - addr_width + i];
    end

    encrypted_addr = sp_decrypt(addr, addr_width, nonce);
    return encrypted_addr;

  endfunction : decrypt_sram_addr

  // SRAM data encryption is more involved, we need to run 2 rounds of PRINCE on the nonce and key
  // and then XOR the result with the data.
  //
  // After that, the XORed data neeeds to them be passed through the S&P network one byte at a time.
  function automatic state_t encrypt_sram_data(logic data[], int data_width, int sp_width,
                                               logic addr[], int addr_width,
                                               logic key[], logic nonce[]);
    logic keystream[] = new[SRAM_BLOCK_WIDTH];
    logic data_enc[] = new[data_width];
    logic byte_to_enc[] = new[8];
    logic enc_byte[] = new[8];
    logic zero_key[] = new[data_width];
    int   ks_width = (data_width < 64) ? data_width : 64;

    // the key used for byte diffusion is all-zero.
    for (int i = 0; i < data_width; i++) begin
      zero_key[i] = '0;
    end

    // Generate the keystream
    keystream = gen_keystream(addr, addr_width, key, nonce);

    // XOR keystream with input data
    // Assumes ks_width <= 64.
    for (int i = 0; i < data_width; i++) begin
      data_enc[i] = data[i] ^ keystream[i % ks_width];
    end

    if (data_width == sp_width) begin
      // pass the entire word through the subst/perm network at once (the next cases would give the
      // same results too, but this should be a bit more efficient)
      data_enc = sp_encrypt(data_enc, data_width, zero_key);
    end else if (sp_width == 8) begin
      // pass each byte of the encoded result through the subst/perm network (special case of the
      // general code below)
      for (int i = 0; i < data_width / 8; i++) begin
        byte_to_enc = data_enc[i*8 +: 8];
        enc_byte = sp_encrypt(byte_to_enc, 8, zero_key);
        data_enc[i*8 +: 8] = enc_byte;
      end
    end else begin
      // divide the word into sp_width chunks to pass it through the subst/perm network
      for (int chunk_lsb = 0; chunk_lsb < data_width; chunk_lsb += sp_width) begin
        int bits_remaining = data_width - chunk_lsb;
        int chunk_width = (bits_remaining < sp_width) ? bits_remaining : sp_width;
        logic chunk[] = new[chunk_width];

        for (int j = 0; j < chunk_width; j++) begin
          chunk[j] = data_enc[chunk_lsb + j];
        end
        chunk = sp_encrypt(chunk, chunk_width, zero_key);
        for (int j = 0; j < chunk_width; j++) begin
          data_enc[chunk_lsb + j] = chunk[j];
        end
      end
    end
    return data_enc;

  endfunction : encrypt_sram_data

  function automatic state_t decrypt_sram_data(logic data[], int data_width, int sp_width,
                                               logic addr[], int addr_width,
                                               logic key[], logic nonce[]);
    logic keystream[] = new[SRAM_BLOCK_WIDTH];
    logic data_dec[] = new[data_width];
    logic byte_to_dec[] = new[8];
    logic dec_byte[] = new[8];
    logic zero_key[] = new[data_width];
    int   ks_width = (data_width < 64) ? data_width : 64;

    // the key used for byte diffusion is all-zero.
    for (int i = 0; i < data_width; i++) begin
      zero_key[i] = '0;
    end

    // Generate the keystream
    keystream = gen_keystream(addr, addr_width, key, nonce);

    if (data_width == sp_width) begin
      // pass the entire word through the subst/perm network at once (the next cases would give the
      // same results too, but this should be a bit more efficient)
      data_dec = sp_decrypt(data, data_width, zero_key);
    end else if (sp_width == 8) begin
      // pass each byte of the data through the subst/perm network (special case of the general code
      // below)
      for (int i = 0; i < data_width / 8; i++) begin
        byte_to_dec = data[i*8 +: 8];
        dec_byte = sp_decrypt(byte_to_dec, 8, zero_key);
        data_dec[i*8 +: 8] = dec_byte;
      end
    end else begin
      // divide the word into sp_width chunks to pass it through the subst/perm network
      for (int chunk_lsb = 0; chunk_lsb < data_width; chunk_lsb += sp_width) begin
        int bits_remaining = data_width - chunk_lsb;
        int chunk_width = (bits_remaining < sp_width) ? bits_remaining : sp_width;
        logic chunk[] = new[chunk_width];

        for (int j = 0; j < chunk_width; j++) begin
          chunk[j] = data[chunk_lsb + j];
        end
        chunk = sp_decrypt(chunk, chunk_width, zero_key);
        for (int j = 0; j < chunk_width; j++) begin
          data_dec[chunk_lsb + j] = chunk[j];
        end
      end
    end

    // XOR result data with the keystream
    for (int i = 0; i < data_width; i++) begin
      data_dec[i] = data_dec[i] ^ keystream[i % ks_width];
    end

    return data_dec;

  endfunction : decrypt_sram_data

endpackage : sram_scrambler_pkg
