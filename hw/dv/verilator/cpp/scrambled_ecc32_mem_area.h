// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_DV_VERILATOR_CPP_SCRAMBLED_ECC32_MEM_AREA_H_
#define OPENTITAN_HW_DV_VERILATOR_CPP_SCRAMBLED_ECC32_MEM_AREA_H_

#include <vector>

#include "ecc32_mem_area.h"

/**
 * A memory that implements scrambling over a 32-bit ECC integrity protection
 * scheme storing 39 = 32 + 7 bits of physical data for each 32 bits of logical
 * data.
 */
class ScrambledEcc32MemArea : public Ecc32MemArea {
 public:
  /**
   * Constructor
   *
   * Create an ScrambledEcc32MemArea that will connect to a SystemVerilog memory
   * at scope. It is size words long. Each memory word is 4 * width_32 bytes
   * wide in the address space and 39 * width_32 bits wide in the physical
   * memory.
   *
   * If the keystream of one single PRINCE instance should be repeated,
   * set "repeat_keystream" to true. If this is set to false, multiple
   * PRINCE instances are employed to produce the keystream.
   *
   */
  ScrambledEcc32MemArea(const std::string &scope, uint32_t size,
                        uint32_t width_32, bool repeat_keystream = true);

 private:
  void WriteBuffer(uint8_t buf[SV_MEM_WIDTH_BYTES],
                   const std::vector<uint8_t> &data, size_t start_idx,
                   uint32_t dst_word) const override;

  void ReadBuffer(std::vector<uint8_t> &data,
                  const uint8_t buf[SV_MEM_WIDTH_BYTES],
                  uint32_t src_word) const override;

  uint32_t ToPhysAddr(uint32_t logical_addr) const override;

  uint32_t GetPhysWidth() const;
  uint32_t GetPhysWidthByte() const;
  uint32_t GetPrinceReplications() const;
  uint32_t GetNonceWidth() const;
  uint32_t GetNonceWidthByte() const;

  std::vector<uint8_t> GetScrambleKey() const;
  std::vector<uint8_t> GetScrambleNonce() const;

  std::string scr_scope_;
  uint32_t addr_width_;
  bool repeat_keystream_;
};

#endif  // OPENTITAN_HW_DV_VERILATOR_CPP_SCRAMBLED_ECC32_MEM_AREA_H_
