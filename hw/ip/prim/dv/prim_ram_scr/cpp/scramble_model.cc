// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "scramble_model.h"

#include <algorithm>
#include <cassert>
#include <functional>
#include <iostream>
#include <stdint.h>
#include <vector>

#include "prince_ref.h"

uint8_t PRESENT_SBOX4[] = {0xc, 0x5, 0x6, 0xb, 0x9, 0x0, 0xa, 0xd,
                           0x3, 0xe, 0xf, 0x8, 0x4, 0x7, 0x1, 0x2};

uint8_t PRESENT_SBOX4_INV[] = {0x5, 0xe, 0xf, 0x8, 0xc, 0x1, 0x2, 0xd,
                               0xb, 0x4, 0x6, 0x3, 0x0, 0x7, 0x9, 0xa};

static const uint32_t kNumAddrSubstPermRounds = 2;
static const uint32_t kNumDataSubstPermRounds = 2;
static const uint32_t kNumPrinceHalfRounds = 2;

static std::vector<uint8_t> byte_reverse_vector(
    const std::vector<uint8_t> &vec_in) {
  std::vector<uint8_t> vec_out(vec_in.size());

  std::reverse_copy(std::begin(vec_in), std::end(vec_in), std::begin(vec_out));

  return vec_out;
}

static uint8_t read_vector_bit(const std::vector<uint8_t> &vec,
                               uint32_t bit_pos) {
  assert(bit_pos / 8 < vec.size());

  return (vec[bit_pos / 8] >> (bit_pos % 8)) & 1;
}

static void or_vector_bit(std::vector<uint8_t> &vec, uint32_t bit_pos,
                          uint8_t bit) {
  assert(bit_pos / 8 < vec.size());

  vec[bit_pos / 8] |= bit << (bit_pos % 8);
}

static std::vector<uint8_t> xor_vectors(const std::vector<uint8_t> &vec_a,
                                        const std::vector<uint8_t> &vec_b) {
  assert(vec_a.size() == vec_b.size());

  std::vector<uint8_t> vec_out(vec_a.size());

  std::transform(vec_a.begin(), vec_a.end(), vec_b.begin(), vec_out.begin(),
                 std::bit_xor<uint8_t>{});

  return vec_out;
}

// Run each 4-bit chunk of bytes from `in` through the SBOX. Where `bit_width`
// isn't a multiple of 4 the remaining bits are just copied straight through.
// `invert` choose whether to use the inverted SBOX or not.
static std::vector<uint8_t> scramble_sbox_layer(const std::vector<uint8_t> &in,
                                                uint32_t bit_width,
                                                uint8_t sbox[16]) {
  assert(in.size() == ((bit_width + 7) / 8));
  std::vector<uint8_t> out(in.size(), 0);

  // Iterate through each 4 bit chunk of the data and apply the appropriate SBOX
  for (int i = 0; i < bit_width / 4; ++i) {
    uint8_t sbox_in, sbox_out;

    sbox_in = in[i / 2];

    int shift = (i % 2) ? 4 : 0;
    sbox_in = (sbox_in >> shift) & 0xf;

    sbox_out = sbox[sbox_in];

    out[i / 2] |= sbox_out << shift;
  }

  // Where bit_width is not a multiple of 4 copy over the remaining bits
  if (bit_width % 4) {
    int shift = ((bit_width % 8) >= 4) ? 4 : 0;
    uint8_t nibble = (in[bit_width / 8] >> shift) & 0xf;
    out[bit_width / 8] |= nibble << shift;
  }

  return out;
}

// Reverse bits from incoming byte vector
static std::vector<uint8_t> scramble_flip_layer(const std::vector<uint8_t> &in,
                                                uint32_t bit_width) {
  assert(in.size() == ((bit_width + 7) / 8));
  std::vector<uint8_t> out(in.size(), 0);

  for (int i = 0; i < bit_width; ++i) {
    or_vector_bit(out, bit_width - i - 1, read_vector_bit(in, i));
  }

  return out;
}

// Apply butterfly to incoming byte vector. Even bits are placed in the lower
// half of the output, odd bits are placed in the upper half of the output.
static std::vector<uint8_t> scramble_perm_layer(const std::vector<uint8_t> &in,
                                                uint32_t bit_width,
                                                bool invert) {
  assert(in.size() == ((bit_width + 7) / 8));
  std::vector<uint8_t> out(in.size(), 0);

  for (int i = 0; i < bit_width / 2; ++i) {
    if (invert) {
      or_vector_bit(out, i * 2, read_vector_bit(in, i));
      or_vector_bit(out, i * 2 + 1, read_vector_bit(in, i + (bit_width / 2)));
    } else {
      or_vector_bit(out, i, read_vector_bit(in, i * 2));
      or_vector_bit(out, i + (bit_width / 2), read_vector_bit(in, i * 2 + 1));
    }
  }

  if (bit_width % 2) {
    // Where bit_width isn't even, the final bit is copied across to the same
    // position
    or_vector_bit(out, bit_width - 1, read_vector_bit(in, bit_width - 1));
  }

  return out;
}

// Apply a full set of subsitution/permutation rounds for encrypt to the
// incoming byte vector
static std::vector<uint8_t> scramble_subst_perm_enc(
    const std::vector<uint8_t> &in, const std::vector<uint8_t> &key,
    uint32_t bit_width, uint32_t num_rounds) {
  assert(in.size() == ((bit_width + 7) / 8));
  assert(key.size() == ((bit_width + 7) / 8));

  std::vector<uint8_t> state(in);

  for (int i = 0; i < num_rounds; ++i) {
    state = xor_vectors(state, key);

    state = scramble_sbox_layer(state, bit_width, PRESENT_SBOX4);
    state = scramble_flip_layer(state, bit_width);
    state = scramble_perm_layer(state, bit_width, false);
  }

  state = xor_vectors(state, key);

  return state;
}

// Apply a full set of substitution/permutation rounds for decrypt to the
// incoming byte vector
static std::vector<uint8_t> scramble_subst_perm_dec(
    const std::vector<uint8_t> &in, const std::vector<uint8_t> &key,
    uint32_t bit_width, uint32_t num_rounds) {
  assert(in.size() == ((bit_width + 7) / 8));
  assert(key.size() == ((bit_width + 7) / 8));

  std::vector<uint8_t> state(in);

  for (int i = 0; i < num_rounds; ++i) {
    state = xor_vectors(state, key);

    state = scramble_perm_layer(state, bit_width, true);
    state = scramble_flip_layer(state, bit_width);
    state = scramble_sbox_layer(state, bit_width, PRESENT_SBOX4_INV);
  }

  state = xor_vectors(state, key);

  return state;
}

// Generate a keystream for XORing with data using PRINCE.
// If repeat_keystream is set to true, the output from one PRINCE instance is
// repeated when the keystream is greater than a single PRINCE width (64bit).
// Otherwise, multiple PRINCEs are instantiated to form the keystream.
static std::vector<uint8_t> scramble_gen_keystream(
    const std::vector<uint8_t> &addr, uint32_t addr_width,
    const std::vector<uint8_t> &nonce, const std::vector<uint8_t> &key,
    uint32_t keystream_width, uint32_t num_half_rounds, bool repeat_keystream) {
  assert(key.size() == (kPrinceWidthByte * 2));

  // Determine how many PRINCE replications are required
  uint32_t num_princes, num_repetitions;
  if (repeat_keystream) {
    num_princes = 1;
    num_repetitions = (keystream_width + kPrinceWidth - 1) / kPrinceWidth;
  } else {
    num_princes = (keystream_width + kPrinceWidth - 1) / kPrinceWidth;
    num_repetitions = 1;
  }

  std::vector<uint8_t> keystream;

  for (int i = 0; i < num_princes; ++i) {
    // Initial vector is data for PRINCE to encrypt. Formed from nonce and data
    // address
    std::vector<uint8_t> iv(8, 0);

    for (int j = 0; j < kPrinceWidth; ++j) {
      if (j < addr_width) {
        // Bottom addr_width bits of IV are address
        or_vector_bit(iv, j, read_vector_bit(addr, j));
      } else {
        // Other bits are taken from nonce. Each PRINCE instantiation will use
        // different nonce bits.
        int nonce_bit = (j - addr_width) + i * (kPrinceWidth - addr_width);
        or_vector_bit(iv, j, read_vector_bit(nonce, nonce_bit));
      }
    }

    // PRINCE C reference model works on big-endian byte order
    iv = byte_reverse_vector(iv);
    auto key_be = byte_reverse_vector(key);

    // Apply PRINCE to IV to produce keystream
    std::vector<uint8_t> keystream_block(kPrinceWidthByte);
    prince_enc_dec(&iv[0], &key_be[0], &keystream_block[0], 0, num_half_rounds,
                   0);

    // Flip keystream into little endian order and add to keystream vector
    keystream_block = byte_reverse_vector(keystream_block);
    // Repeat the output of a single PRINCE instance if needed
    for (int k = 0; k < num_repetitions; ++k) {
      keystream.insert(keystream.end(), keystream_block.begin(),
                       keystream_block.end());
    }
  }

  // Total keystream bits generated are some multiple of kPrinceWidth. This can
  // result in unused keystream bits. Remove the unused bytes from the keystream
  // vector and zero out top unused bits in the final byte if required.
  uint32_t keystream_bytes = (keystream_width + 7) / 8;
  uint32_t keystream_bytes_to_erase = keystream.size() - keystream_bytes;
  if (keystream_bytes_to_erase) {
    keystream.erase(keystream.end() - keystream_bytes_to_erase,
                    keystream.end());
  }

  if (keystream_width % 8) {
    keystream[keystream.size() - 1] &= (1 << (keystream_width % 8)) - 1;
  }

  return keystream;
}

// Split incoming data into subst_perm_width chunks and individually apply the
// substitution/permutation layer to each
static std::vector<uint8_t> scramble_subst_perm_full_width(
    const std::vector<uint8_t> &in, uint32_t bit_width,
    uint32_t subst_perm_width, bool enc) {
  assert(in.size() == ((bit_width + 7) / 8));

  // Determine how many bytes each subst_perm_width chunk is and how many
  // chunks are needed to cover the full bit_width.
  uint32_t subst_perm_bytes = (subst_perm_width + 7) / 8;
  uint32_t subst_perm_blocks =
      (bit_width + subst_perm_width - 1) / subst_perm_width;

  std::vector<uint8_t> out(in.size(), 0);
  std::vector<uint8_t> zero_key(subst_perm_bytes, 0);

  auto sp_scrambler = enc ? scramble_subst_perm_enc : scramble_subst_perm_dec;

  for (int i = 0; i < subst_perm_blocks; ++i) {
    // Where bit_width does not evenly divide into subst_perm_width the
    // final block is smaller.
    uint32_t bits_so_far = subst_perm_width * i;
    uint32_t block_width = std::min(subst_perm_width, bit_width - bits_so_far);

    std::vector<uint8_t> subst_perm_data(subst_perm_bytes, 0);

    // Extract bits from in for this chunk
    for (int j = 0; j < block_width; ++j) {
      or_vector_bit(subst_perm_data, j,
                    read_vector_bit(in, j + i * subst_perm_width));
    }

    // Apply the substitution/permutation layer to the chunk
    auto subst_perm_out = sp_scrambler(subst_perm_data, zero_key, block_width,
                                       kNumDataSubstPermRounds);

    // Write the result to the `out` vector
    for (int j = 0; j < block_width; ++j) {
      or_vector_bit(out, j + i * subst_perm_width,
                    read_vector_bit(subst_perm_out, j));
    }
  }

  return out;
}

std::vector<uint8_t> scramble_addr(const std::vector<uint8_t> &addr_in,
                                   uint32_t addr_width,
                                   const std::vector<uint8_t> &nonce,
                                   uint32_t nonce_width) {
  assert(addr_in.size() == ((addr_width + 7) / 8));

  std::vector<uint8_t> addr_enc_nonce(addr_in.size(), 0);

  // Address is scrambled by using substitution/permutation layer with the nonce
  // used as a key.
  // Extract relevant nonce bits for key
  for (int i = 0; i < addr_width; ++i) {
    or_vector_bit(addr_enc_nonce, i,
                  read_vector_bit(nonce, nonce_width - addr_width + i));
  }

  // Apply substitution/permutation layer
  return scramble_subst_perm_enc(addr_in, addr_enc_nonce, addr_width,
                                 kNumAddrSubstPermRounds);
}

std::vector<uint8_t> scramble_encrypt_data(
    const std::vector<uint8_t> &data_in, uint32_t data_width,
    uint32_t subst_perm_width, const std::vector<uint8_t> &addr,
    uint32_t addr_width, const std::vector<uint8_t> &nonce,
    const std::vector<uint8_t> &key, bool repeat_keystream) {
  assert(data_in.size() == ((data_width + 7) / 8));
  assert(addr.size() == ((addr_width + 7) / 8));

  // Data is encrypted by XORing with keystream then applying
  // substitution/permutation layer

  auto keystream =
      scramble_gen_keystream(addr, addr_width, nonce, key, data_width,
                             kNumPrinceHalfRounds, repeat_keystream);

  auto data_enc = xor_vectors(data_in, keystream);

  return scramble_subst_perm_full_width(data_enc, data_width, subst_perm_width,
                                        true);
}

std::vector<uint8_t> scramble_decrypt_data(
    const std::vector<uint8_t> &data_in, uint32_t data_width,
    uint32_t subst_perm_width, const std::vector<uint8_t> &addr,
    uint32_t addr_width, const std::vector<uint8_t> &nonce,
    const std::vector<uint8_t> &key, bool repeat_keystream) {
  assert(data_in.size() == ((data_width + 7) / 8));
  assert(addr.size() == ((addr_width + 7) / 8));

  // Data is decrypted by reversing substitution/permutation layer then XORing
  // with keystream
  auto data_sp_out = scramble_subst_perm_full_width(data_in, data_width,
                                                    subst_perm_width, false);

  auto keystream =
      scramble_gen_keystream(addr, addr_width, nonce, key, data_width,
                             kNumPrinceHalfRounds, repeat_keystream);

  auto data_dec = xor_vectors(data_sp_out, keystream);

  return data_dec;
}
