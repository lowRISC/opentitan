// Copyright lowRISC contributors.
// Copyright 2016 Sebastien Riou
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/*! \file prince_ref.h
    \brief Reference implementation of the Prince block cipher, complient to
   C99. 'Reference' here means straightforward, unoptimized, and checked against
   the few test vectors provided in the original paper
   (http://eprint.iacr.org/2012/529.pdf). By defining the macro PRINCE_PRINT,
   one can print out all successive internal states.
*/

/*
 * This C-implementation of the PRINCE block cipher is taken from Sebastien
 * Riou's open-sourced 'prince-c-ref' GitHub repository, found here:
 * https://github.com/sebastien-riou/prince-c-ref/blob/master/include/prince_ref.h.
 *
 * Several modifications of varying severity have been made to this C model to
 * enable extra external parameterizations for more thorough verification of the
 * OpenTitan PRINCE hardware implementation.
 * These modifications, in no particular order, are:
 *
 *    - Conversion of `prince_enc_dec_uint64_t(...)` to a non-static function to
 *      allow usage by an external DPI-C model.
 *    - Additional arguments added to `prince_enc_dec_uint64_t(...)`,
 *      `prince_enc_dec(...)`, `prince_encrypt(...)` `prince_decrypt(...)`, and
 *      `prince_core(...)` to allow an external DPI-C model to control the
 *      number of cipher half-rounds and to toggle between the "legacy" key
 *      schedule detailed in the original PRINCE paper and a newer key schedule.
 *    - Modification of `prince_core(...)` to handle the new key schedule and
 *      user-specified number of half-rounds.
 */

#ifndef OPENTITAN_HW_IP_PRIM_DV_PRIM_PRINCE_CRYPTO_DPI_PRINCE_PRINCE_REF_H_
#define OPENTITAN_HW_IP_PRIM_DV_PRIM_PRINCE_CRYPTO_DPI_PRINCE_PRINCE_REF_H_

#include <stdint.h>
#include <string.h>

#ifndef PRINCE_PRINT
#define PRINCE_PRINT(a) \
  do {                  \
  } while (0)
#endif

/**
 * Converts a byte array into a 64-bit integer.
 *
 * The byte at index 0 is placed as the most significant byte.
 */
static uint64_t bytes_to_uint64(const uint8_t in[8]) {
  uint64_t out = 0;
  unsigned int i;
  for (i = 0; i < 8; i++)
    out = (out << 8) | in[i];
  return out;
}

/**
 * Converts a 64-bit integer into a byte array.
 *
 * The most significant byte is placed at index 0.
 */
static void uint64_to_bytes(const uint64_t in, uint8_t out[8]) {
  unsigned int i;
  for (i = 0; i < 8; i++)
    out[i] = in >> ((7 - i) * 8);
}

/**
 * Computes K0' from K0.
 */
static uint64_t prince_k0_to_k0_prime(const uint64_t k0) {
  uint64_t k0_ror1 = (k0 >> 1) | (k0 << 63);
  uint64_t k0_prime = k0_ror1 ^ (k0 >> 63);
  return k0_prime;
}

static uint64_t prince_round_constant(const unsigned int round) {
  uint64_t rc[] = {UINT64_C(0x0000000000000000), UINT64_C(0x13198a2e03707344),
                   UINT64_C(0xa4093822299f31d0), UINT64_C(0x082efa98ec4e6c89),
                   UINT64_C(0x452821e638d01377), UINT64_C(0xbe5466cf34e90c6c),
                   UINT64_C(0x7ef84f78fd955cb1), UINT64_C(0x85840851f1ac43aa),
                   UINT64_C(0xc882d32f25323c54), UINT64_C(0x64a51195e0e3610d),
                   UINT64_C(0xd3b5a399ca0c2399), UINT64_C(0xc0ac29b7c97c50dd)};
  return rc[round];
}

/**
 * The 4 bit Prince sbox.
 *
 * Only the 4 lsb are taken into account to preserve nibble granularity.
 */
static unsigned int prince_sbox(unsigned int nibble) {
  const unsigned int sbox[] = {0xb, 0xf, 0x3, 0x2, 0xa, 0xc, 0x9, 0x1,
                               0x6, 0x7, 0x8, 0x0, 0xe, 0x5, 0xd, 0x4};
  return sbox[nibble & 0xF];
}

/**
 * The 4 bit Prince inverse sbox.
 *
 * Only the 4 lsb are taken into account to preserve nibble granularity.
 */
static unsigned int prince_sbox_inv(unsigned int nibble) {
  const unsigned int sbox[] = {0xb, 0x7, 0x3, 0x2, 0xf, 0xd, 0x8, 0x9,
                               0xa, 0x6, 0x4, 0x0, 0x5, 0xe, 0xc, 0x1};
  return sbox[nibble & 0xF];
}

/**
 * The S step of the Prince cipher.
 */
static uint64_t prince_s_layer(const uint64_t s_in) {
  uint64_t s_out = 0;
  for (unsigned int i = 0; i < 16; i++) {
    const unsigned int shift = i * 4;
    const unsigned int sbox_in = s_in >> shift;
    const uint64_t sbox_out = prince_sbox(sbox_in);
    s_out |= sbox_out << shift;
  }
  return s_out;
}

/**
 * The S^-1 step of the Prince cipher.
 */
static uint64_t prince_s_inv_layer(const uint64_t s_inv_in) {
  uint64_t s_inv_out = 0;
  for (unsigned int i = 0; i < 16; i++) {
    const unsigned int shift = i * 4;
    const unsigned int sbox_in = s_inv_in >> shift;
    const uint64_t sbox_out = prince_sbox_inv(sbox_in);
    s_inv_out |= sbox_out << shift;
  }
  return s_inv_out;
}

static uint64_t gf2_mat_mult16_1(const uint64_t in, const uint64_t mat[16]) {
  uint64_t out = 0;
  for (unsigned int i = 0; i < 16; i++) {
    if ((in >> i) & 1)
      out ^= mat[i];
  }
  return out;
}

/**
 * Build Prince's 16 bit matrices M0 and M1.
 */
static void prince_m16_matrices(uint64_t m16[2][16]) {
  // 4 bits matrices m0 to m3 are stored in array m4
  const uint64_t m4[4][4] = {// m0
                             {0x0, 0x2, 0x4, 0x8},
                             // m1
                             {0x1, 0x0, 0x4, 0x8},
                             // m2
                             {0x1, 0x2, 0x0, 0x8},
                             // m3
                             {0x1, 0x2, 0x4, 0x0}};
  // build 16 bits matrices
  for (unsigned int i = 0; i < 16; i++) {
    const unsigned int base = i / 4;
    m16[0][i] =
        (m4[(base + 3) % 4][i % 4] << 8) | (m4[(base + 2) % 4][i % 4] << 4) |
        (m4[(base + 1) % 4][i % 4] << 0) | (m4[(base + 0) % 4][i % 4] << 12);
    m16[1][i] =
        (m16[0][i] >> 12) |
        (0xFFFF & (m16[0][i] << 4));  // m1 is just a rotated version of m0
  }
}

/**
 * The M' step of the Prince cipher.
 */
static uint64_t prince_m_prime_layer(const uint64_t m_prime_in) {
  // 16 bits matrices M0 and M1, generated using the code below
  // uint64_t m16[2][16];prince_m16_matrices(m16);
  // for(unsigned int i=0;i<16;i++) PRINCE_PRINT(m16[0][i]);
  // for(unsigned int i=0;i<16;i++) PRINCE_PRINT(m16[1][i]);
  static const uint64_t m16[2][16] = {
      {0x0111, 0x2220, 0x4404, 0x8088, 0x1011, 0x0222, 0x4440, 0x8808, 0x1101,
       0x2022, 0x0444, 0x8880, 0x1110, 0x2202, 0x4044, 0x0888},

      {0x1110, 0x2202, 0x4044, 0x0888, 0x0111, 0x2220, 0x4404, 0x8088, 0x1011,
       0x0222, 0x4440, 0x8808, 0x1101, 0x2022, 0x0444, 0x8880}};
  const uint64_t chunk0 = gf2_mat_mult16_1(m_prime_in >> (0 * 16), m16[0]);
  const uint64_t chunk1 = gf2_mat_mult16_1(m_prime_in >> (1 * 16), m16[1]);
  const uint64_t chunk2 = gf2_mat_mult16_1(m_prime_in >> (2 * 16), m16[1]);
  const uint64_t chunk3 = gf2_mat_mult16_1(m_prime_in >> (3 * 16), m16[0]);
  const uint64_t m_prime_out = (chunk3 << (3 * 16)) | (chunk2 << (2 * 16)) |
                               (chunk1 << (1 * 16)) | (chunk0 << (0 * 16));
  return m_prime_out;
}

/**
 * The shift row and inverse shift row of the Prince cipher.
 */
static uint64_t prince_shift_rows(const uint64_t in, int inverse) {
  const uint64_t row_mask = UINT64_C(0xF000F000F000F000);
  uint64_t shift_rows_out = 0;
  for (unsigned int i = 0; i < 4; i++) {
    const uint64_t row = in & (row_mask >> (4 * i));
    const unsigned int shift = inverse ? i * 16 : 64 - i * 16;
    shift_rows_out |= (row >> shift) | (row << (64 - shift));
  }
  return shift_rows_out;
}

/**
 * The M step of the Prince cipher.
 */
static uint64_t prince_m_layer(const uint64_t m_in) {
  const uint64_t m_prime_out = prince_m_prime_layer(m_in);
  const uint64_t shift_rows_out = prince_shift_rows(m_prime_out, 0);
  return shift_rows_out;
}

/**
 * The M^-1 step of the Prince cipher.
 */
static uint64_t prince_m_inv_layer(const uint64_t m_inv_in) {
  const uint64_t shift_rows_out = prince_shift_rows(m_inv_in, 1);
  const uint64_t m_prime_out = prince_m_prime_layer(shift_rows_out);
  return m_prime_out;
}

/**
 * The core function of the Prince cipher.
 */
static uint64_t prince_core(const uint64_t core_input, const uint64_t k0_new,
                            const uint64_t k1, int num_half_rounds) {
  PRINCE_PRINT(core_input);
  PRINCE_PRINT(k1);
  uint64_t round_input = core_input ^ k1 ^ prince_round_constant(0);
  for (unsigned int round = 1; round <= num_half_rounds; round++) {
    PRINCE_PRINT(round_input);
    const uint64_t s_out = prince_s_layer(round_input);
    PRINCE_PRINT(s_out);
    const uint64_t m_out = prince_m_layer(s_out);
    PRINCE_PRINT(m_out);
    round_input = (round % 2 == 1)
                      ? m_out ^ k0_new ^ prince_round_constant(round)
                      : m_out ^ k1 ^ prince_round_constant(round);
  }
  const uint64_t middle_round_s_out = prince_s_layer(round_input);
  PRINCE_PRINT(middle_round_s_out);
  const uint64_t m_prime_out = prince_m_prime_layer(middle_round_s_out);
  PRINCE_PRINT(m_prime_out);
  const uint64_t middle_round_s_inv_out = prince_s_inv_layer(m_prime_out);
  round_input = middle_round_s_inv_out;
  // for(unsigned int round = 6; round < num_half_rounds * 2 + 1; round ++){
  for (unsigned int round = 1; round <= num_half_rounds; round++) {
    PRINCE_PRINT(round_input);
    const uint64_t constant_idx = 10 - num_half_rounds + round;
    const uint64_t m_inv_in =
        ((num_half_rounds + round + 1) % 2 == 1)
            ? round_input ^ k0_new ^ prince_round_constant(constant_idx)
            : round_input ^ k1 ^ prince_round_constant(constant_idx);
    PRINCE_PRINT(m_inv_in);
    const uint64_t s_inv_in = prince_m_inv_layer(m_inv_in);
    PRINCE_PRINT(s_inv_in);
    const uint64_t s_inv_out = prince_s_inv_layer(s_inv_in);
    round_input = s_inv_out;
  }
  const uint64_t core_output = round_input ^ k1 ^ prince_round_constant(11);
  PRINCE_PRINT(core_output);
  return core_output;
}

/**
 * Top level function for Prince encryption/decryption.
 *
 * enc_k0 and enc_k1 must be the same for encryption and decryption.
 * The handling of decryption is done internally.
 */
uint64_t prince_enc_dec_uint64(const uint64_t input, const uint64_t enc_k0,
                               const uint64_t enc_k1, int decrypt,
                               int num_half_rounds, int old_key_schedule) {
  const uint64_t prince_alpha = UINT64_C(0xc0ac29b7c97c50dd);
  const uint64_t k1 = enc_k1 ^ (decrypt ? prince_alpha : 0);
  const uint64_t k0_new =
      (old_key_schedule) ? k1 : enc_k0 ^ (decrypt ? prince_alpha : 0);
  const uint64_t enc_k0_prime = prince_k0_to_k0_prime(enc_k0);
  const uint64_t k0 = decrypt ? enc_k0_prime : enc_k0;
  const uint64_t k0_prime = decrypt ? enc_k0 : enc_k0_prime;
  PRINCE_PRINT(k0);
  PRINCE_PRINT(input);
  const uint64_t core_input = input ^ k0;
  const uint64_t core_output =
      prince_core(core_input, k0_new, k1, num_half_rounds);
  const uint64_t output = core_output ^ k0_prime;
  PRINCE_PRINT(k0_prime);
  PRINCE_PRINT(output);
  return output;
}

/**
 * Byte oriented top level function for Prince encryption/decryption.
 *
 * key_bytes 0 to 7 must contain K0.
 * key_bytes 8 to 15 must contain K1.
 */
static void prince_enc_dec(const uint8_t in_bytes[8],
                           const uint8_t key_bytes[16], uint8_t out_bytes[8],
                           int decrypt, int num_half_rounds,
                           int old_key_schedule) {
  const uint64_t input = bytes_to_uint64(in_bytes);
  const uint64_t enc_k0 = bytes_to_uint64(key_bytes);
  const uint64_t enc_k1 = bytes_to_uint64(key_bytes + 8);
  const uint64_t output = prince_enc_dec_uint64(
      input, enc_k0, enc_k1, decrypt, num_half_rounds, old_key_schedule);
  uint64_to_bytes(output, out_bytes);
}

/**
 * Byte oriented top level function for Prince encryption.
 *
 * key_bytes 0 to 7 must contain K0.
 * key_bytes 8 to 15 must contain K1.
 */
static void prince_encrypt(const uint8_t in_bytes[8],
                           const uint8_t key_bytes[16], uint8_t out_bytes[8],
                           int num_half_rounds, int old_key_schedule) {
  prince_enc_dec(in_bytes, key_bytes, out_bytes, 0, num_half_rounds,
                 old_key_schedule);
}

/**
 * Byte oriented top level function for Prince decryption.
 *
 * key_bytes 0 to 7 must contain K0.
 * key_bytes 8 to 15 must contain K1.
 */
static void prince_decrypt(const uint8_t in_bytes[8],
                           const uint8_t key_bytes[16], uint8_t out_bytes[8],
                           int num_half_rounds, int old_key_schedule) {
  prince_enc_dec(in_bytes, key_bytes, out_bytes, 1, num_half_rounds,
                 old_key_schedule);
  uint64_t m16[2][16];
}

#endif  // OPENTITAN_HW_IP_PRIM_DV_PRIM_PRINCE_CRYPTO_DPI_PRINCE_PRINCE_REF_H_
