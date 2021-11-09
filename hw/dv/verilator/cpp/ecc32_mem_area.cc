// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "ecc32_mem_area.h"
#include "secded_enc.h"

#include <cassert>
#include <cstring>
#include <stdexcept>

Ecc32MemArea::Ecc32MemArea(const std::string &scope, uint32_t size,
                           uint32_t width_32)
    : MemArea(scope, size, 4 * width_32) {
  // Check that multiplying by 4 didn't discard a bit
  assert(4 * width_32 > width_32);

  // No need to worry about ranges here: we've checked in the base class that
  // width_byte isn't too big.
  uint32_t phy_width_bits = 39 * width_32;

  // This is a stronger check than the one in the base class (which
  // makes sure there's enough space for the un-expanded memory width)
  assert(phy_width_bits <= SV_MEM_WIDTH_BITS);
}

void Ecc32MemArea::LoadVmem(const std::string &path) const {
  throw std::runtime_error(
      "vmem files are not supported for memories with ECC bits");
}

// Add bits to buf at bit_idx
//
// buf is assumed to be little-endian, so bit_idx 0 will refer to the bottom
// bit of buf[0] and bit_idx 15 will refer to the top bit of buf[1].
//
// This takes the bottom count bits from new_bits (where count <= 8). It
// assumes that the relevant place in buf is zeroed (simplifying the
// read-modify-write cycle).
static void insert_bits(uint8_t *buf, unsigned bit_idx, uint8_t new_bits,
                        unsigned count) {
  assert(count <= 8);

  buf += bit_idx / 8;
  bit_idx = bit_idx % 8;

  while (count) {
    unsigned space_avail = 8 - bit_idx;
    unsigned to_take = std::min(space_avail, count);

    uint8_t masked = ((1 << to_take) - 1) & new_bits;
    uint8_t shifted = masked << bit_idx;

    *buf |= shifted;

    ++buf;
    bit_idx = 0;
    count -= to_take;
    new_bits >>= to_take;
  }
}

// Extract bits from buf at bit_idx
static uint8_t extract_bits(const uint8_t *buf, unsigned bit_idx,
                            unsigned count) {
  assert(count <= 8);

  uint8_t ret = 0;
  unsigned out_idx = 0;

  buf += bit_idx / 8;
  bit_idx = bit_idx % 8;

  while (count) {
    unsigned bits_avail = 8 - bit_idx;
    unsigned to_take = std::min(bits_avail, count);

    uint8_t shifted = *buf >> bit_idx;
    uint8_t masked = shifted & ((1 << to_take) - 1);

    ret |= masked << out_idx;

    ++buf;
    bit_idx = 0;
    count -= to_take;
    out_idx += to_take;
  }

  return ret;
}

void Ecc32MemArea::WriteBuffer(uint8_t buf[SV_MEM_WIDTH_BYTES],
                               const std::vector<uint8_t> &data,
                               size_t start_idx, uint32_t dst_word) const {
  // The insert_bits routine assumes that the buffer will have been zeroed, so
  // do that here. Note that this buffer has (width_byte_ / 4) words, each of
  // which is 39 bits long. Divide this by 8, rounding up.
  size_t phys_size_bytes = (39 * (width_byte_ / 4) + 7) / 8;
  memset(buf, 0, phys_size_bytes);

  for (int i = 0; i < width_byte_ / 4; ++i) {
    uint8_t check_bits = enc_secded_39_32(&data[start_idx + 4 * i]);
    for (int j = 0; j < 4; ++j) {
      insert_bits(buf, 39 * i + 8 * j, data[start_idx + 4 * i + j], 8);
    }
    insert_bits(buf, 39 * i + 32, check_bits, 7);
  }
}

void Ecc32MemArea::ReadBuffer(std::vector<uint8_t> &data,
                              const uint8_t buf[SV_MEM_WIDTH_BYTES],
                              uint32_t src_word) const {
  for (int i = 0; i < width_byte_ / 4; ++i) {
    for (int j = 0; j < 4; ++j) {
      data.push_back(extract_bits(buf, 39 * i + 8 * j, 8));
    }
  }
}
