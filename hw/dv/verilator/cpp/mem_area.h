// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_DV_VERILATOR_CPP_MEM_AREA_H_
#define OPENTITAN_HW_DV_VERILATOR_CPP_MEM_AREA_H_

#include <cstdint>
#include <string>
#include <vector>

// This is the maximum width of a memory that's supported by the code in
// prim_util_memload.svh
#define SV_MEM_WIDTH_BITS 312
#define SV_MEM_WIDTH_BYTES ((SV_MEM_WIDTH_BITS + 7) / 8)

/**
 * A "memory area", representing a memory in the simulated design.
 */
class MemArea {
 public:
  /** Constructor
   *
   * @param scope  The SystemVerilog scope where the instantiated memory can be
   *               found. This needs to support the DPI-C interfaces \c
   *               simutil_memload and \c simutil_set_mem (used for vmem and
   *               ELF files, respectively).
   *
   * @param size   The size of the memory in bytes (must be positive and a
   *               multiple of \p width_byte)
   *
   * @param size   The width of each entry in bytes (must be positive)
   */
  MemArea(const std::string &scope, uint32_t size, uint32_t width_byte);

  virtual ~MemArea() {}

  /** Write data to this memory area at the given word offset
   *
   * This assumes that the result will fit in the memory. If the scope cannot
   * be set, this throws an SVScoped::Error. If a call to \c simutil_set_mem
   * fails, this throws a \c std::runtime_error.
   *
   * @param word_offset The offset, in words, of the first word that should be
   *                    written.
   *
   * @param data        The data that should be written. If the length is not a
   *                    multiple of \p word_offset, the last word will be
   *                    zero-extended.
   */
  virtual void Write(uint32_t word_offset,
                     const std::vector<uint8_t> &data) const;

  /** Read data from this memory area, starting at the given offset.
   *
   * This assumes that there are <tt>word_offset + num_words</tt> words in the
   * memory. Returns a vector with <tt>num_words * width_byte_</tt> elements.
   *
   * If the scope cannot be set, this throws an SVScoped::Error. If a call to
   * simutil_get_mem fails, this throws a std::runtime_error.
   *
   * @param word_offset The offset, in words, of the first word that should be
   *                    written.
   *
   * @param num_words   The number of words to read.
   */
  virtual std::vector<uint8_t> Read(uint32_t word_offset,
                                    uint32_t num_words) const;

  /** Use \c simutil_memload to load a vmem file into the memory */
  virtual void LoadVmem(const std::string &path) const;

  const std::string &GetScope() const { return scope_; }
  uint32_t GetSizeWords() const { return num_words_; }
  uint32_t GetSizeBytes() const { return num_words_ * width_byte_; }
  uint32_t GetWidthByte() const { return width_byte_; }
  uint32_t GetWidth() const { return 8 * width_byte_; }

 protected:
  std::string scope_;    ///< Design scope (used for accesses over DPI)
  uint32_t num_words_;   ///< Size of the memory area in words
  uint32_t width_byte_;  ///< Size of each word in bytes

  /** Write to buf with the data that should be copied to the physical memory
   * for a single memory word.
   *
   * The default implementation just uses memcpy to copy the data across. Other
   * implementations might add scrambling, ECC bits or similar. This must write
   * every bit of buf that will be used by the memory, but needn't clear bits
   * further up (this is done outside of the loop).
   *
   * @param buf       Destination buffer
   * @param data      A large buffer that contains the data to be written
   * @param start_idx An offset into \p data for the start of the memory word
   * @param dst_word  Logical address of the location being written
   */
  virtual void WriteBuffer(uint8_t buf[SV_MEM_WIDTH_BYTES],
                           const std::vector<uint8_t> &data, size_t start_idx,
                           uint32_t dst_word) const;

  /** Extract the logical memory contents corresponding to the physical
   * memory contents in \p buf and append them to \p data.
   *
   * The default implementation just uses \c std::copy_n to copy the data
   * across. Other implementations might undo scrambling, remove ECC bits or
   * similar.
   *
   * @param data     The target, onto which the extracted memory contents should
   * be appended.
   *
   * @param buf      Source buffer (physical memory bits)
   * @param src_word Logical address of the location being read
   */
  virtual void ReadBuffer(std::vector<uint8_t> &data,
                          const uint8_t buf[SV_MEM_WIDTH_BYTES],
                          uint32_t src_word) const;

  /** Convert a logical address to physical address
   *
   * Some memories may have a mapping between the address supplied on the
   * request and the physical address used to access the memory array (for
   * example scrambled memories). By default logical and physical address are
   * the same.
   */
  virtual uint32_t ToPhysAddr(uint32_t logical_addr) const {
    return logical_addr;
  }
};

#endif  // OPENTITAN_HW_DV_VERILATOR_CPP_MEM_AREA_H_
