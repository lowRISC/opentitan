// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "scrambled_ecc32_mem_area.h"

#include <algorithm>
#include <cassert>
#include <iostream>
#include <sstream>

#include "scramble_model.h"
#include "sv_scoped.h"

// This is the maximum width of a nonce that's supported by the code in
// prim_util_get_scramble_key_nonce.svh
static const uint32_t kScrMaxNonceWidth = 320;
static const uint32_t kScrMaxNonceWidthByte = (kScrMaxNonceWidth + 7) / 8;

// Functions to convert from integer address to/from a little-endian vector of
// bytes, addr_width is given in bits
static std::vector<uint8_t> AddrIntToBytes(uint32_t addr, uint32_t addr_width) {
  uint32_t addr_width_bytes = (addr_width + 7) / 8;
  std::vector<uint8_t> addr_bytes(addr_width_bytes);

  for (int i = 0; i < addr_width_bytes; ++i) {
    addr_bytes[i] = addr & 0xff;
    addr >>= 8;
  }

  return addr_bytes;
}

static uint32_t AddrBytesToInt(const std::vector<uint8_t> &addr) {
  assert(addr.size() <= 4);

  uint32_t addr_out = 0;
  int cur_shift = 0;

  for (int i = 0; i < addr.size(); ++i) {
    addr_out |= (addr[i] << cur_shift);
    cur_shift += 8;
  }

  return addr_out;
}

// Converts svBitVecVal (bit[m:n] SV type) into a byte vector
static std::vector<uint8_t> ByteVecFromSV(svBitVecVal sv_val[],
                                          uint32_t bytes) {
  int shift = 0;
  std::vector<uint8_t> vec(bytes);
  for (int i = 0; i < bytes; ++i) {
    vec[i] = (sv_val[i / 4] >> shift) & 0xff;

    shift += 8;
    if (shift == 32) {
      shift = 0;
    }
  }

  return vec;
}

// Analogous to the vbits SystemVerilog function from prim_util_pkg.sv. It
// calculates the number of bits needed to address size items.
static uint32_t vbits(uint32_t size) {
  assert(size > 0);

  if (size == 1) {
    return 1;
  }

  size -= 1;
  uint32_t width = 0;
  while (size) {
    width++;
    size /= 2;
  }

  return width;
}

extern "C" {
int simutil_get_scramble_key(svBitVecVal *key);
int simutil_get_scramble_nonce(svBitVecVal *nonce);
}

std::vector<uint8_t> ScrambledEcc32MemArea::GetScrambleKey() const {
  SVScoped scoped(scr_scope_);
  svBitVecVal key_minibuf[((kPrinceWidthByte * 2) + 3) / 4];

  if (!simutil_get_scramble_key(key_minibuf)) {
    std::ostringstream oss;
    oss << "Could not read key at scope " << scr_scope_;
    throw std::runtime_error(oss.str());
  }

  return ByteVecFromSV(key_minibuf, kPrinceWidthByte * 2);
}

std::vector<uint8_t> ScrambledEcc32MemArea::GetScrambleNonce() const {
  assert(GetNonceWidthByte() <= kScrMaxNonceWidthByte);

  SVScoped scoped(scr_scope_);
  svBitVecVal nonce_minibuf[(kScrMaxNonceWidthByte + 3) / 4];

  if (!simutil_get_scramble_nonce((svBitVecVal *)nonce_minibuf)) {
    std::ostringstream oss;
    oss << "Could not read nonce at scope " << scr_scope_;
    throw std::runtime_error(oss.str());
  }

  return ByteVecFromSV(nonce_minibuf, GetNonceWidthByte());
}

ScrambledEcc32MemArea::ScrambledEcc32MemArea(const std::string &scope,
                                             uint32_t size, uint32_t width_32,
                                             bool repeat_keystream)
    : Ecc32MemArea(
          SVScoped::join_sv_scopes(
              scope, "u_prim_ram_1p_adv.u_mem.gen_generic.u_impl_generic"),
          size, width_32),
      scr_scope_(scope) {
  addr_width_ = vbits(size);
  repeat_keystream_ = repeat_keystream;
}

uint32_t ScrambledEcc32MemArea::GetPhysWidth() const {
  return (GetWidthByte() / 4) * 39;
}

uint32_t ScrambledEcc32MemArea::GetPhysWidthByte() const {
  return (GetPhysWidth() + 7) / 8;
}

uint32_t ScrambledEcc32MemArea::GetPrinceReplications() const {
  if (repeat_keystream_) {
    return 1;
  } else {
    return (GetPhysWidthByte() + 7) / 8;
  }
}

uint32_t ScrambledEcc32MemArea::GetNonceWidth() const {
  return GetPrinceReplications() * 64;
}

uint32_t ScrambledEcc32MemArea::GetNonceWidthByte() const {
  return GetPrinceReplications() * 8;
}

void ScrambledEcc32MemArea::WriteBuffer(uint8_t buf[SV_MEM_WIDTH_BYTES],
                                        const std::vector<uint8_t> &data,
                                        size_t start_idx,
                                        uint32_t dst_word) const {
  // Compute integrity
  Ecc32MemArea::WriteBuffer(buf, data, start_idx, dst_word);

  std::vector<uint8_t> scramble_buf =
      std::vector<uint8_t>(buf, buf + GetPhysWidthByte());

  // Scramble data with integrity
  scramble_buf = scramble_encrypt_data(
      scramble_buf, GetPhysWidth(), 39, AddrIntToBytes(dst_word, addr_width_),
      addr_width_, GetScrambleNonce(), GetScrambleKey(), repeat_keystream_);

  // Copy scrambled data to write buffer
  std::copy(scramble_buf.begin(), scramble_buf.end(), &buf[0]);
}

void ScrambledEcc32MemArea::ReadBuffer(std::vector<uint8_t> &data,
                                       const uint8_t buf[SV_MEM_WIDTH_BYTES],
                                       uint32_t src_word) const {
  // Unscramble data from read buffer
  std::vector<uint8_t> scrambled_data =
      std::vector<uint8_t>(buf, buf + GetPhysWidthByte());
  std::vector<uint8_t> unscrambled_data = scramble_decrypt_data(
      scrambled_data, GetPhysWidth(), 39, AddrIntToBytes(src_word, addr_width_),
      addr_width_, GetScrambleNonce(), GetScrambleKey(), repeat_keystream_);

  // Strip integrity to give final result
  Ecc32MemArea::ReadBuffer(data, &unscrambled_data[0], src_word);
}

uint32_t ScrambledEcc32MemArea::ToPhysAddr(uint32_t logical_addr) const {
  // Scramble logical address to get physical address
  return AddrBytesToInt(scramble_addr(AddrIntToBytes(logical_addr, addr_width_),
                                      addr_width_, GetScrambleNonce(),
                                      GetNonceWidth()));
}
