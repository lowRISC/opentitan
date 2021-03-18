// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "ecc32_mem_area.h"

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

void Ecc32MemArea::WriteBuffer(uint8_t buf[SV_MEM_WIDTH_BYTES],
                               const std::vector<uint8_t> &data,
                               size_t start_idx) const {
  int log_width_32 = width_byte_ / 4;
  int phy_width_bits = 39 * log_width_32;
  int phy_width_bytes = (phy_width_bits + 7) / 8;

  // Start by collecting our width_byte_ input bytes into (width_byte_ / 4)
  // 32-bit groupings and adding check bits. (Eventually, we'll be adding
  // proper ECC check bits here but, since we're not checking yet, let's
  // zero-pad for now).
  //
  // TODO: Add proper ECC check bits here!
  struct expanded_t {
    uint8_t bytes[5];
  };

  std::vector<expanded_t> expanded(log_width_32);
  for (int i = 0; i < log_width_32; ++i) {
    // Store things little-endian, so the "real bits" go in bytes 0 to 3 and
    // the check bits go in byte 4. Bytes 5 to 7 are zero.
    expanded_t next;
    memcpy(next.bytes, &data[start_idx + 4 * i], 4);
    next.bytes[4] = 0;
    expanded[i] = next;
  }

  // Now write to buf, pulling 39 bits from each element of in_64.
  for (int i = 0; i < phy_width_bytes; ++i) {
    uint8_t acc = 0;
    int out_lsb = 0;

    int in_word_idx = (8 * i) / 39;
    int in_word_lsb = (8 * i) % 39;

    int bits_left = 8;
    while (bits_left) {
      int in_byte_idx = in_word_lsb / 8;
      int in_byte_lsb = in_word_lsb % 8;

      int byte_width = (in_byte_idx == 4) ? 7 : 8;
      int bits_at_byte = std::min(byte_width - in_byte_lsb, bits_left);

      uint8_t in_data = expanded[in_word_idx].bytes[in_byte_idx] >> in_byte_lsb;
      uint8_t in_mask = (((uint32_t)1 << bits_at_byte) - 1) & 0xff;

      acc |= (in_data & in_mask) << out_lsb;

      out_lsb += bits_at_byte;
      if (in_byte_idx == 4) {
        ++in_word_idx;
        in_word_lsb = 0;
      } else {
        in_word_lsb += bits_at_byte;
      }

      bits_left -= bits_at_byte;
    }
    buf[i] = acc;
  }
}

void Ecc32MemArea::ReadBuffer(std::vector<uint8_t> &data,
                              const uint8_t buf[SV_MEM_WIDTH_BYTES]) const {
  for (int i = 0; i < width_byte_; ++i) {
    int in_word = i / 4;

    int in_idx = (7 * in_word + 8 * i) / 8;
    int in_lsb = (7 * in_word + 8 * i) % 8;

    uint8_t acc = 0;

    int bits_left = 8;
    int out_lsb = 0;

    while (bits_left) {
      uint8_t in_data = buf[in_idx] >> in_lsb;

      int bits_at_idx = std::min(8 - in_lsb, bits_left);

      // The mask for the bits to take from in_data.
      uint8_t in_mask = ((1u << bits_at_idx) - 1) & 0xff;

      acc |= (in_data & in_mask) << out_lsb;

      in_lsb = 0;
      out_lsb += bits_at_idx;
      bits_left -= bits_at_idx;
      ++in_idx;
    }

    data.push_back(acc);
  }
}
