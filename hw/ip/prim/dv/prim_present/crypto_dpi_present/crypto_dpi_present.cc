// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Simple unhardened reference implementation of the PRESENT cipher, following
// the description in
//
//   [1] Bognadov et al, PRESENT: An Ultra-Lightweight Block Cipher. LNCS 4727:
//       450–466. doi:10.1007/978-3-540-74735-2_31.

#include <cassert>
#include <cstdint>
#include <svdpi.h>
#include <vector>

static const uint8_t sbox4[16] = {0xc, 0x5, 0x6, 0xb, 0x9, 0x0, 0xa, 0xd,
                                  0x3, 0xe, 0xf, 0x8, 0x4, 0x7, 0x1, 0x2};

static const uint8_t sbox4_inv[16] = {0x5, 0xe, 0xf, 0x8, 0xc, 0x1, 0x2, 0xd,
                                      0xb, 0x4, 0x6, 0x3, 0x0, 0x7, 0x9, 0xa};

static const uint8_t bit_perm[64] = {
    0,  16, 32, 48, 1,  17, 33, 49, 2,  18, 34, 50, 3,  19, 35, 51,
    4,  20, 36, 52, 5,  21, 37, 53, 6,  22, 38, 54, 7,  23, 39, 55,
    8,  24, 40, 56, 9,  25, 41, 57, 10, 26, 42, 58, 11, 27, 43, 59,
    12, 28, 44, 60, 13, 29, 45, 61, 14, 30, 46, 62, 15, 31, 47, 63};

static const uint8_t bit_perm_inv[64] = {
    0, 4, 8,  12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60,
    1, 5, 9,  13, 17, 21, 25, 29, 33, 37, 41, 45, 49, 53, 57, 61,
    2, 6, 10, 14, 18, 22, 26, 30, 34, 38, 42, 46, 50, 54, 58, 62,
    3, 7, 11, 15, 19, 23, 27, 31, 35, 39, 43, 47, 51, 55, 59, 63};

static uint64_t mask64(int bits) { return ((uint64_t)1 << bits) - 1; }

namespace {
struct key128_t {
  uint64_t hi, lo;
};

class PresentState {
 public:
  PresentState(unsigned key_size, key128_t key);

  // This is the body of the for loop in Fig. 1 of the paper ([1], above). If
  // is_last_round, then it also includes the call to addRoundKey that follows.
  uint64_t enc_round(uint64_t input, unsigned round, bool is_last_round) const;

  // The inverse of enc_round. Note that a decryption should start with a high
  // round and with is_last_round set, then count down.
  uint64_t dec_round(uint64_t input, unsigned round, bool is_last_round) const;

 private:
  static key128_t next_round_key(const key128_t &k, unsigned key_size,
                                 unsigned round_count);

  static uint64_t add_round_key(uint64_t data, const key128_t &k,
                                unsigned key_size);
  static uint64_t sbox_layer(bool inverse, uint64_t data);
  static uint64_t perm_layer(bool inverse, uint64_t data);

  unsigned key_size;
  std::vector<key128_t> key_schedule;
};
}  // namespace

PresentState::PresentState(unsigned key_size, key128_t key)
    : key_size(key_size) {
  assert(key_size == 80 || key_size == 128);
  key_schedule.reserve(32);
  key_schedule.push_back(key);
  for (int i = 1; i <= 31; ++i) {
    key = next_round_key(key, key_size, i);
    key_schedule.push_back(key);
  }
}

uint64_t PresentState::enc_round(uint64_t input, unsigned round,
                                 bool is_last_round) const {
  assert(1 <= round && round < key_schedule.size());
  const key128_t &key = key_schedule[round - 1];

  // addRoundKey
  uint64_t w1 = add_round_key(input, key, key_size);

  // sBoxLayer
  uint64_t w2 = sbox_layer(false, w1);

  // pLayer
  uint64_t w3 = perm_layer(false, w2);

  // On the final round, call addRoundKey with the following key.
  uint64_t w4 =
      is_last_round ? add_round_key(w3, key_schedule[round], key_size) : w3;

  return w4;
}

uint64_t PresentState::dec_round(uint64_t input, unsigned round,
                                 bool is_last_round) const {
  assert(1 <= round && round < key_schedule.size());
  const key128_t &key = key_schedule[round - 1];

  // If we're undoing the last round, start by calling addRoundKey with the
  // following key.
  uint64_t w1 = is_last_round
                    ? add_round_key(input, key_schedule[round], key_size)
                    : input;

  // pLayer^{-1}
  uint64_t w2 = perm_layer(true, w1);

  // sBoxLayer^{-1}
  uint64_t w3 = sbox_layer(true, w2);

  // addRoundKey
  uint64_t w4 = add_round_key(w3, key, key_size);

  return w4;
}

key128_t PresentState::next_round_key(const key128_t &k, unsigned key_size,
                                      unsigned round_count) {
  assert((round_count >> 5) == 0);
  assert(key_size == 80 || key_size == 128);

  if (key_size == 80) {
    assert((k.hi >> 16) == 0);

    // Rotate the key left by 61 bits
    //
    // The top word (bits 79:64) will come from bits (18:3). The
    // bottom word (bits 63:0) will have bits 2:0 at the top, then
    // bits 79:64 (from the top word) and finally bits 63:19.
    uint64_t rot_hi = (k.lo >> 3) & mask64(16);
    uint64_t rot_lo =
        ((((k.lo >> 0) & mask64(3)) << 61) | (((k.hi >> 0)) << 45) |
         (((k.lo >> 19) & mask64(45)) << 0));
    assert((rot_hi >> 16) == 0);

    // Pass the top 4 bits through sbox4
    uint64_t subst_hi =
        (((uint64_t)sbox4[rot_hi >> 12] << 12) | (rot_hi & mask64(12)));
    uint64_t subst_lo = rot_lo;

    // XOR bits 19:15 with the round counter
    uint64_t xored_hi = subst_hi;
    uint64_t xored_lo =
        ((subst_lo & ~mask64(20)) |
         ((((subst_lo >> 15) & mask64(5)) ^ round_count) << 15) |
         (subst_lo >> 0 & mask64(15)));

    key128_t next = {.hi = xored_hi, .lo = xored_lo};
    return next;
  } else {
    // Rotate the key left by 61 bits
    //
    // The top word (bits 127:64) will come from bits 66:64 (from the
    // top word) and then bits 63:3 (from the bottom word). The bottom
    // word (bits 63:0) will have bits 2:0 at the top and then bits
    // 127:67.
    uint64_t rot_hi = (((k.hi & mask64(3)) << 61) | (k.lo >> 3));
    uint64_t rot_lo = (((k.lo & mask64(3)) << 61) | (k.hi >> 3));

    // Pass top 8 bits through a pair of sbox4's
    uint64_t rot_nib124 = (rot_hi >> 60) & mask64(4);
    uint64_t rot_nib120 = (rot_hi >> 56) & mask64(4);

    uint64_t subst_hi =
        (((uint64_t)sbox4[rot_nib124] << 60) |
         ((uint64_t)sbox4[rot_nib120] << 56) | (rot_hi & mask64(56)));
    uint64_t subst_lo = rot_lo;

    // XOR bits 66:62
    uint64_t xored_hi = subst_hi ^ ((uint64_t)round_count >> 2);
    uint64_t xored_lo = subst_lo ^ ((uint64_t)round_count << 62);

    key128_t next = {.hi = xored_hi, .lo = xored_lo};
    return next;
  }
}

uint64_t PresentState::add_round_key(uint64_t data, const key128_t &k,
                                     unsigned key_size) {
  assert(key_size == 80 || key_size == 128);
  uint64_t k64 = (key_size == 80) ? ((k.hi << 48) | (k.lo >> 16)) : k.hi;
  return data ^ k64;
}

uint64_t PresentState::sbox_layer(bool inverse, uint64_t data) {
  uint64_t ret = 0;
  for (int i = 0; i < 64 / 4; ++i) {
    unsigned nibble = (data >> (4 * i)) & 0xf;
    uint64_t subst = inverse ? sbox4_inv[nibble] : sbox4[nibble];
    ret |= subst << (4 * i);
  }
  return ret;
}

uint64_t PresentState::perm_layer(bool inverse, uint64_t data) {
  uint64_t ret = 0;
  for (int i = 0; i < 64; ++i) {
    uint64_t bit = (data >> i) & 1;
    ret |= bit << (inverse ? bit_perm_inv[i] : bit_perm[i]);
  }
  return ret;
}

extern "C" {

PresentState *c_dpi_present_mk(unsigned key_size, const svBitVecVal *key) {
  assert(key_size == 80 || key_size == 128);

  // Each element of key represents 32 bits. Unpack into a key128_t, zeroing
  // the top bits if key size was 80.
  uint32_t w32s[4];
  for (int i = 0; i < 4; ++i) {
    unsigned lsb = 32 * i;
    unsigned bits_left = (lsb < key_size) ? key_size - lsb : 0;
    unsigned mask =
        (bits_left < 32) ? ((uint32_t)1 << bits_left) - 1 : ~(uint32_t)0;
    w32s[i] = key[i] & mask;
  }
  key128_t k128 = {.hi = ((uint64_t)w32s[3] << 32) | w32s[2],
                   .lo = ((uint64_t)w32s[1] << 32) | w32s[0]};

  return new PresentState(key_size, k128);
}

void c_dpi_present_free(PresentState *ps) { delete ps; }

void c_dpi_present_enc_round(const PresentState *ps, unsigned round,
                             unsigned char is_last_round,
                             const svBitVecVal *src, svBitVecVal *dst) {
  assert(ps);
  assert(is_last_round == 0 || is_last_round == 1);

  uint64_t in64 = ((uint64_t)src[1] << 32) | src[0];
  uint64_t out64 = ps->enc_round(in64, round, is_last_round != 0);

  dst[1] = out64 >> 32;
  dst[0] = (uint32_t)out64;
}

void c_dpi_present_dec_round(const PresentState *ps, unsigned round,
                             unsigned char is_last_round,
                             const svBitVecVal *src, svBitVecVal *dst) {
  assert(ps);
  assert(is_last_round == 0 || is_last_round == 1);

  uint64_t in64 = ((uint64_t)src[1] << 32) | src[0];
  uint64_t out64 = ps->dec_round(in64, round, is_last_round != 0);

  dst[1] = out64 >> 32;
  dst[0] = (uint32_t)out64;
}
}
