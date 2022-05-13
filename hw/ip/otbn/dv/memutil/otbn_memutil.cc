// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "otbn_memutil.h"

#include <cassert>
#include <cstring>
#include <gelf.h>
#include <iostream>
#include <libelf.h>
#include <limits>
#include <regex>
#include <sstream>
#include <stdexcept>

#include "scrambled_ecc32_mem_area.h"
#include "sv_scoped.h"
#include "sv_utils.h"

OtbnMemUtil::OtbnMemUtil(const std::string &top_scope)
    : imem_(SVScoped::join_sv_scopes(top_scope, "u_imem"), 4096 / 4, 4 / 4),
      dmem_(SVScoped::join_sv_scopes(top_scope, "u_dmem"), 4096 / 32, 32 / 4),
      expected_end_addr_(-1) {
  RegisterMemoryArea("imem", 0x4000, &imem_);
  RegisterMemoryArea("dmem", 0x8000, &dmem_);
}

void OtbnMemUtil::LoadElf(const std::string &elf_path) {
  LoadElfToMemories(false, elf_path);
}

const StagedMem::SegMap &OtbnMemUtil::GetSegs(bool is_imem) const {
  return GetMemoryData(is_imem ? "imem" : "dmem").GetSegs();
}

uint32_t OtbnMemUtil::GetLoopWarp(uint32_t addr, uint32_t from_cnt) const {
  auto key = std::make_pair(addr, from_cnt);
  auto it = loop_warp_.find(key);
  return (it == loop_warp_.end()) ? from_cnt : it->second;
}

void OtbnMemUtil::OnElfLoaded(Elf *elf_file) {
  assert(elf_file);

  expected_end_addr_ = -1;
  loop_warp_.clear();

  // Look through the symbol table of elf_file for an expected end
  // address and any loop warping symbols.
  Elf_Scn *scn = nullptr;
  while ((scn = elf_nextscn(elf_file, scn))) {
    Elf32_Shdr *shdr = elf32_getshdr(scn);
    assert(shdr);
    if (shdr->sh_type != SHT_SYMTAB)
      continue;

    Elf_Data *sec_data = elf_getdata(scn, nullptr);
    assert(sec_data);

    int num_syms = shdr->sh_size / shdr->sh_entsize;
    for (int i = 0; i < num_syms; ++i) {
      GElf_Sym sym;
      gelf_getsym(sec_data, i, &sym);

      const char *sym_name = elf_strptr(elf_file, shdr->sh_link, sym.st_name);
      if (!sym_name)
        continue;

      OnSymbol(sym_name, sym.st_value);
    }
    break;
  }
}

void OtbnMemUtil::OnSymbol(const std::string &name, uint32_t value) {
  // Expected end address
  if (name == "_expected_end_addr") {
    expected_end_addr_ = value;
  }

  // Loop warping. These symbols are of the form "_loop_warp_FROM_TO_*" where
  // FROM and TO are decimal loop counts and the value of the symbol is the
  // address where it should apply. Trailing junk is allowed (to ensure
  // uniqueness).
  std::regex lw_re("_loop_warp_([0-9]+)_([0-9]+).*");
  std::smatch lw_match;
  if (std::regex_match(name, lw_match, lw_re)) {
    assert(lw_match.size() == 3);

    // Parse the "from" count. We know that the captured group is one or
    // more decimal digits, so the only question of correctness is whether
    // it's in range or not. For the "from" count, we know that the loop
    // counter in the design is only 32 bits so if the value is out of range
    // then we just ignore it: it can never match anyway.
    errno = 0;
    unsigned long from_cnt = strtoul(lw_match[1].str().c_str(), nullptr, 10);
    bool good_from_cnt =
        (errno == 0) && (from_cnt <= std::numeric_limits<uint32_t>::max());

    // Parse the "to" count. Again, the only question is whether it's in range
    // or not. Saturate to the maximum value of a uint32: since the design has a
    // 32-bit loop counter, this will always jump to the last iteration.
    unsigned long to_cnt = strtoul(lw_match[2].str().c_str(), nullptr, 10);
    uint32_t to_cnt32 =
        std::min(to_cnt, (unsigned long)std::numeric_limits<uint32_t>::max());

    if (good_from_cnt) {
      AddLoopWarp(value, static_cast<uint32_t>(from_cnt), to_cnt32);
    }
  }
}

void OtbnMemUtil::AddLoopWarp(uint32_t addr, uint32_t from_cnt,
                              uint32_t to_cnt) {
  auto key = std::make_pair(addr, from_cnt);
  auto pr = loop_warp_.insert(std::make_pair(key, to_cnt));
  if (!pr.second) {
    // We didn't actually insert anything, which means that there was already a
    // value stored for this address/from_cnt pair. Since the ordering of ELF
    // symbols isn't something that the user can control, we don't really have a
    // sensible behaviour at this point: throw an error.
    std::ostringstream oss;
    oss << "Duplicate loop warp symbols for address 0x" << std::hex << addr
        << " and initial count " << std::dec << from_cnt << ".";
    throw std::runtime_error(oss.str());
  }
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
  assert(num_segs < (unsigned)std::numeric_limits<int>::max());

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

int OtbnMemUtilGetExpEndAddr(OtbnMemUtil *mem_util) {
  assert(mem_util);
  return mem_util->GetExpEndAddr();
}

svBit OtbnMemUtilGetLoopWarp(OtbnMemUtil *mem_util,
                             /* bit [31:0] */ const svBitVecVal *addr,
                             /* bit [31:0] */ const svBitVecVal *from_cnt,
                             /* output bit [31:0] */ svBitVecVal *to_cnt) {
  assert(mem_util);
  uint32_t addr32 = get_sv_u32(addr);
  uint32_t from32 = get_sv_u32(from_cnt);
  uint32_t to32 = mem_util->GetLoopWarp(addr32, from32);
  set_sv_u32(to_cnt, to32);
  return to32 != from32;
}

int OtbnMemUtilGetNumLoopWarps(OtbnMemUtil *mem_util) {
  assert(mem_util);

  size_t sz = mem_util->GetLoopWarps().size();
  assert(sz < (unsigned)std::numeric_limits<int>::max());

  return sz;
}

void OtbnMemUtilGetLoopWarpByIndex(
    OtbnMemUtil *mem_util, int idx,
    /* output bit [31:0] */ svBitVecVal *addr,
    /* output bit [31:0] */ svBitVecVal *from_cnt,
    /* output bit [31:0] */ svBitVecVal *to_cnt) {
  assert(mem_util);
  assert(0 <= idx);

  auto &warps = mem_util->GetLoopWarps();
  assert((unsigned)idx < warps.size());

  auto it = std::next(warps.begin(), idx);

  uint32_t addr32 = it->first.first;
  uint32_t from32 = it->first.second;
  uint32_t to32 = it->second;

  set_sv_u32(addr, addr32);
  set_sv_u32(from_cnt, from32);
  set_sv_u32(to_cnt, to32);
}
