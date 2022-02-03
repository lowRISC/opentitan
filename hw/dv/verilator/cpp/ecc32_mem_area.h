// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_DV_VERILATOR_CPP_ECC32_MEM_AREA_H_
#define OPENTITAN_HW_DV_VERILATOR_CPP_ECC32_MEM_AREA_H_

#include "mem_area.h"

/**
 * A memory that implements 32-bit ECC, storing 39 = 32 + 7 bits of physical
 * data for each 32 bits of logical data.
 */
class Ecc32MemArea : public MemArea {
 public:
  /**
   * Constructor
   *
   * Create an Ecc32MemArea that will connect to a SystemVerilog memory at
   * scope. It is size words long. Each memory word is 4 * width_32 bytes wide
   * in the address space and 39 * width_32 bits wide in the physical memory.
   */
  Ecc32MemArea(const std::string &scope, uint32_t size, uint32_t width_32);

  void LoadVmem(const std::string &path) const override;

  typedef std::pair<bool, uint32_t> EccWord;
  typedef std::vector<EccWord> EccWords;

  /** Read data with validity bits, starting at the given offset.
   *
   * This is equivalent to MemArea's Read method, but returns 32 bit
   * words, each with a boolean saying whether the integrity bits for
   * that word are valid or not.
   *
   * @param word_offset The offset, in words, of the first word that should be
   *                    read.
   *
   * @param num_words   The number of words to read.
   */
  EccWords ReadWithIntegrity(uint32_t word_offset, uint32_t num_words) const;

  /** Write data with validity bits, starting at the given offset
   *
   * This is equivalent to MemArea's Write method, but takes a vector of pairs
   * with a bit saying whether the integrity bits for the word are valid or
   * not.
   *
   * @param word_offset The offset, in words, of the first word that should be
   *                    written.
   *
   * @param data        The data that should be written.
   */
  void WriteWithIntegrity(uint32_t word_offset, const EccWords &data) const;

 protected:
  void WriteBuffer(uint8_t buf[SV_MEM_WIDTH_BYTES],
                   const std::vector<uint8_t> &data, size_t start_idx,
                   uint32_t dst_word) const override;

  void ReadBuffer(std::vector<uint8_t> &data,
                  const uint8_t buf[SV_MEM_WIDTH_BYTES],
                  uint32_t src_word) const override;

  /** Extract the logical words corresponding to the physical memory contents
   * in \p buf, together with validity bits. Append them to \p data.
   *
   * @param data     The target, onto which the extracted memory words should
   *                 be appended.
   *
   * @param buf      Source buffer (physical memory bits)
   *
   * @param src_word Logical address of the location being read
   */
  virtual void ReadBufferWithIntegrity(EccWords &data,
                                       const uint8_t buf[SV_MEM_WIDTH_BYTES],
                                       uint32_t src_word) const;

  /** Insert a memory word into buf from one or more 32-bit words in data.
   *
   * @param buf       Destination buffer (physical memory bits)
   *
   * @param data      Source data, from which the 32-bit words should be read
   *
   * @param start_idx The index of the first 32-bit word in data to read
   *
   * @param dst_word  Logical address of the location being written
   */
  virtual void WriteBufferWithIntegrity(uint8_t buf[SV_MEM_WIDTH_BYTES],
                                        const EccWords &data, size_t start_idx,
                                        uint32_t dst_word) const;
};

#endif  // OPENTITAN_HW_DV_VERILATOR_CPP_ECC32_MEM_AREA_H_
