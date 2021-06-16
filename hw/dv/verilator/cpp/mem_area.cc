// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "mem_area.h"

#include <algorithm>
#include <cassert>
#include <cstring>
#include <sstream>

#include "sv_scoped.h"

// DPI exports, defined in prim_util_memload.svh
extern "C" {
void simutil_memload(const char *file);
int simutil_set_mem(int index, const svBitVecVal *val);
int simutil_get_mem(int index, svBitVecVal *val);
}

MemArea::MemArea(const std::string &scope, uint32_t num_words,
                 uint32_t width_byte)
    : scope_(scope), num_words_(num_words), width_byte_(width_byte) {
  assert(0 < num_words);
  assert(width_byte <= SV_MEM_WIDTH_BYTES);
}

void MemArea::Write(uint32_t word_offset,
                    const std::vector<uint8_t> &data) const {
  // This "mini buffer" is used to transfer each write to SystemVerilog.
  // `simutil_set_mem` takes a fixed SV_MEM_WIDTH_BITS-bit vector but it will
  // only use the bits required for the RAM width. As an example, for a 32-bit
  // wide RAM only elements 3:0 of `minibuf` will be written to memory. Since
  // the simulator may still read bits from minibuf it does not use, we must
  // use a fixed allocation of the full bit vector size to avoid an out of
  // bounds access.
  uint8_t minibuf[SV_MEM_WIDTH_BYTES];
  memset(minibuf, 0, sizeof minibuf);
  assert(width_byte_ <= sizeof minibuf);

  uint32_t data_words = (data.size() + width_byte_ - 1) / width_byte_;
  assert(word_offset + data_words <= num_words_);

  for (uint32_t i = 0; i < data_words; ++i) {
    uint32_t dst_word = word_offset + i;
    uint32_t phys_addr = ToPhysAddr(dst_word);

    WriteBuffer(minibuf, data, i * width_byte_, dst_word);

    // Both ToPhysAddr and WriteBuffer might set the scope with `SVScoped` so
    // only construct `SVScoped` once they've both been called so they don't
    // interact causing incorrect relative path behaviour. If this fails to set
    // scope, it will throw an error which should be caught at this function's
    // callsite.
    SVScoped scoped(scope_);
    if (!simutil_set_mem(phys_addr, (svBitVecVal *)minibuf)) {
      std::ostringstream oss;
      oss << "Could not set memory at byte offset 0x" << std::hex
          << dst_word * width_byte_ << ".";
      throw std::runtime_error(oss.str());
    }
  }
}

std::vector<uint8_t> MemArea::Read(uint32_t word_offset,
                                   uint32_t num_words) const {
  assert(word_offset + num_words <= num_words_);

  uint32_t num_bytes = width_byte_ * num_words;
  assert(num_words <= num_bytes);

  // See Write for an explanation for this buffer.
  uint8_t minibuf[SV_MEM_WIDTH_BYTES];
  memset(minibuf, 0, sizeof minibuf);
  assert(width_byte_ <= sizeof minibuf);

  std::vector<uint8_t> ret;
  ret.reserve(num_bytes);

  for (uint32_t i = 0; i < num_words; ++i) {
    uint32_t src_word = word_offset + i;
    uint32_t phys_addr = ToPhysAddr(src_word);

    {
      // Both ToPhysAddr and ReadBuffer might set the scope with `SVScoped`.
      // Keep the `SVScoped` here confined to an inner scope so they don't
      // interact causing incorrect relative path behaviour. If this fails to
      // set scope, it will throw an error which should be caught at this
      // function's callsite.
      SVScoped scoped(scope_);
      if (!simutil_get_mem(phys_addr, (svBitVecVal *)minibuf)) {
        std::ostringstream oss;
        oss << "Could not read memory at byte offset 0x" << std::hex
            << src_word * width_byte_ << ".";
        throw std::runtime_error(oss.str());
      }
    }

    ReadBuffer(ret, minibuf, src_word);
  }

  return ret;
}

void MemArea::LoadVmem(const std::string &path) const {
  SVScoped scoped(scope_.c_str());
  // TODO: Add error handling.
  simutil_memload(path.c_str());
}

void MemArea::WriteBuffer(uint8_t buf[SV_MEM_WIDTH_BYTES],
                          const std::vector<uint8_t> &data, size_t start_idx,
                          uint32_t dst_word) const {
  size_t words_left = data.size() - start_idx;
  size_t to_copy = std::min(words_left, (size_t)width_byte_);
  if (to_copy < width_byte_) {
    memset(buf, 0, SV_MEM_WIDTH_BYTES);
  }
  memcpy(buf, &data[start_idx], to_copy);
}

void MemArea::ReadBuffer(std::vector<uint8_t> &data,
                         const uint8_t buf[SV_MEM_WIDTH_BYTES],
                         uint32_t src_word) const {
  // Append the first width_byte_ bytes of buf to data.
  std::copy_n(reinterpret_cast<const char *>(buf), width_byte_,
              std::back_inserter(data));
}
