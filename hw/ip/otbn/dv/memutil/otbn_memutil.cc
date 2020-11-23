// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "otbn_memutil.h"

#include <cassert>
#include <cstring>
#include <iostream>
#include <limits>
#include <stdexcept>

OtbnMemUtil::OtbnMemUtil(const std::string &top_scope) {
  MemAreaLoc imem_loc = {.base = 0x4000, .size = 4096};
  std::string imem_scope =
      top_scope + ".u_imem.u_mem.gen_generic.u_impl_generic";
  if (!RegisterMemoryArea("imem", imem_scope, 32, &imem_loc)) {
    throw std::runtime_error("Failed to register IMEM OTBN memory area.");
  }

  MemAreaLoc dmem_loc = {.base = 0x8000, .size = 4096};
  std::string dmem_scope =
      top_scope + ".u_dmem.u_mem.gen_generic.u_impl_generic";
  if (!RegisterMemoryArea("dmem", dmem_scope, 256, &dmem_loc)) {
    throw std::runtime_error("Failed to register DMEM OTBN memory area.");
  }
}

void OtbnMemUtil::LoadElf(const std::string &elf_path) {
  LoadElfToMemories(false, elf_path);
}

const StagedMem::SegMap &OtbnMemUtil::GetSegs(bool is_imem) const {
  return GetMemoryData(is_imem ? "imem" : "dmem").GetSegs();
}

extern "C" OtbnMemUtil *OtbnMemUtilMake(const char *top_scope) {
  try {
    return new OtbnMemUtil(top_scope);
  } catch (const std::exception &err) {
    std::cerr << "Failed to create OtbnMemUtil: " << err.what() << "\n";
    return nullptr;
  }
}

extern "C" void OtbnMemUtilFree(OtbnMemUtil *mem_util) { delete mem_util; }

extern "C" svBit OtbnMemUtilLoadElf(OtbnMemUtil *mem_util,
                                    const char *elf_path) {
  assert(mem_util);
  assert(elf_path);
  try {
    mem_util->LoadElf(elf_path);
    return sv_1;
  } catch (const std::exception &err) {
    std::cerr << "Failed to load ELF file from `" << elf_path
              << "': " << err.what() << "\n";
    return sv_0;
  }
}

extern "C" svBit OtbnMemUtilStageElf(OtbnMemUtil *mem_util,
                                     const char *elf_path) {
  assert(mem_util);
  assert(elf_path);
  try {
    mem_util->StageElf(false, elf_path);
    return sv_1;
  } catch (const std::exception &err) {
    std::cerr << "Failed to load ELF file from `" << elf_path
              << "': " << err.what() << "\n";
    return sv_0;
  }
}

extern "C" int OtbnMemUtilGetSegCount(OtbnMemUtil *mem_util, svBit is_imem) {
  assert(mem_util);
  const StagedMem::SegMap &segs = mem_util->GetSegs(is_imem);
  size_t num_segs = segs.size();

  // Since the segments are disjoint and 32-bit aligned, there are at most 2^30
  // of them (this, admittedly, would mean an ELF file with a billion segments,
  // but it's theoretically possible). Fortunately, that number is still
  // representable with a signed 32-bit integer, so this assertion shouldn't
  // ever fire.
  assert(num_segs < std::numeric_limits<int>::max());

  return num_segs;
}

extern "C" svBit OtbnMemUtilGetSegInfo(OtbnMemUtil *mem_util, svBit is_imem,
                                       int seg_idx, svBitVecVal *seg_off,
                                       svBitVecVal *seg_size) {
  assert(mem_util);
  assert(seg_off);
  assert(seg_size);

  const StagedMem::SegMap &segs = mem_util->GetSegs(is_imem);

  // Make sure there is such an index.
  if ((seg_idx < 0) || ((unsigned)seg_idx > segs.size())) {
    std::cerr << "Invalid segment index: " << seg_idx << ". "
              << (is_imem ? 'I' : 'D') << "MEM has " << segs.size()
              << " segments.\n";
    return sv_0;
  }

  // Walk to the desired segment (which we know is safe because we just checked
  // the index was valid).
  auto it = std::next(segs.begin(), seg_idx);

  uint32_t seg_addr = it->first.lo;

  // We know that seg_addr must be 32 bit aligned because DpiMemUtil checks its
  // segments are aligned to the memory word size (which is 32 or 256 bits for
  // imem/dmem, respectively).
  assert(seg_addr % 4 == 0);

  uint32_t word_seg_addr = seg_addr / 4;

  size_t size_bytes = it->second.size();

  // We know the size can't be too enormous, because the segment fits in a
  // 32-bit address space.
  assert(size_bytes < std::numeric_limits<uint32_t>::max());

  // Divide by 4 to get the number of 32 bit words. Round up: we'll pad out the
  // data with zeros if there's a ragged edge. (We know this is valid because
  // any next range is also 32 bit aligned).
  uint32_t size_words = ((uint64_t)size_bytes + 3) / 4;

  memcpy(seg_off, &word_seg_addr, sizeof(uint32_t));
  memcpy(seg_size, &size_words, sizeof(uint32_t));

  return sv_1;
}

extern "C" svBit OtbnMemUtilGetSegData(
    OtbnMemUtil *mem_util, svBit is_imem, int word_off,
    /* output bit[31:0] */ svBitVecVal *data_value) {
  assert(mem_util);
  assert(data_value);

  if ((word_off < 0) ||
      ((unsigned)word_off > std::numeric_limits<uint32_t>::max() / 4)) {
    std::cerr << "Invalid word offset: " << word_off << ".\n";
    return sv_0;
  }

  uint32_t byte_addr = (unsigned)word_off * 4;

  const StagedMem::SegMap &segs = mem_util->GetSegs(is_imem);

  auto it = segs.find(byte_addr);
  if (it == segs.end()) {
    return sv_0;
  }

  uint32_t seg_addr = it->first.lo;
  assert(seg_addr <= byte_addr);

  // The offset within the segment
  uint32_t seg_off = byte_addr - seg_addr;
  assert(seg_off < it->second.size());

  // How many bytes are available in the segment, starting at seg_off? We know
  // this will be positive (because RangeMap::find finds us a range that
  // includes seg_addr and then DpiMemUtil makes sure that the value at that
  // range is the right length).
  size_t avail = it->second.size() - seg_off;
  size_t to_copy = std::min(avail, (size_t)4);

  // Copy data from the segment into a uint32_t. Zero-initialize it, in case
  // to_copy < 4.
  uint32_t data = 0;
  memcpy(&data, &it->second[seg_off], to_copy);

  // Now copy that uint32_t into data_value and return success.
  memcpy(data_value, &data, 4);
  return sv_1;
}
