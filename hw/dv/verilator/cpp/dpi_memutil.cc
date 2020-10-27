// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "dpi_memutil.h"

#include <cassert>
#include <cstring>
#include <fcntl.h>
#include <iostream>
#include <libelf.h>
#include <sstream>
#include <sys/stat.h>
#include <unistd.h>
#include <vector>

#include "sv_scoped.h"

// DPI Exports
extern "C" {

/**
 * Write |file| to a memory
 *
 * @param file path to a SystemVerilog $readmemh()-compatible file (VMEM file)
 */
extern void simutil_memload(const char *file);

/**
 * Write a 32 bit word |val| to memory at index |index|
 *
 * @return 1 if successful, 0 otherwise
 */
extern int simutil_set_mem(int index, const svBitVecVal *val);
}

namespace {
// Convenience class for runtime errors when loading an ELF file
class ElfError : public std::exception {
 public:
  ElfError(const std::string &path, const std::string &msg) {
    std::ostringstream oss;
    oss << "Failed to load ELF file at `" << path << "': " << msg;
    msg_ = oss.str();
  }

  const char *what() const noexcept override { return msg_.c_str(); }

 private:
  std::string msg_;
};

// Class wrapping an open ELF file
class ElfFile {
 public:
  ElfFile(const std::string &path) : path_(path) {
    (void)elf_errno();
    if (elf_version(EV_CURRENT) == EV_NONE) {
      throw std::runtime_error(elf_errmsg(-1));
    }

    fd_ = open(path.c_str(), O_RDONLY, 0);
    if (fd_ < 0) {
      throw ElfError(path, "could not open file.");
    }

    ptr_ = elf_begin(fd_, ELF_C_READ, NULL);
    if (!ptr_) {
      close(fd_);
      throw ElfError(path, elf_errmsg(-1));
    }

    if (elf_kind(ptr_) != ELF_K_ELF) {
      elf_end(ptr_);
      close(fd_);
      throw ElfError(path, "not an ELF file.");
    }
  }

  ~ElfFile() {
    elf_end(ptr_);
    close(fd_);
  }

  size_t GetPhdrNum() {
    size_t phnum;
    if (elf_getphdrnum(ptr_, &phnum) != 0) {
      throw ElfError(path_, elf_errmsg(-1));
    }
    return phnum;
  }

  const Elf32_Phdr *GetPhdrs() {
    const Elf32_Phdr *phdrs = elf32_getphdr(ptr_);
    if (!phdrs)
      throw ElfError(path_, elf_errmsg(-1));
    return phdrs;
  }

  std::string path_;
  int fd_;
  Elf *ptr_;
};
}  // namespace

// Convert a string to a MemImageType, throwing a std::runtime_error
// if it's not a known name.
static MemImageType GetMemImageTypeByName(const std::string &name) {
  if (name == "elf")
    return kMemImageElf;
  if (name == "vmem")
    return kMemImageVmem;

  std::ostringstream oss;
  oss << "Unknown image type: `" << name << "'.";
  throw std::runtime_error(oss.str());
}

// Return a MemImageType for the file at filepath or throw a std::runtime_error.
// Never returns kMemImageUnknown.
static MemImageType DetectMemImageType(const std::string &filepath) {
  size_t ext_pos = filepath.find_last_of(".");
  if (ext_pos == std::string::npos) {
    // Assume ELF files if no file extension is given.
    // TODO: Make this more robust by actually checking the file contents.
    return kMemImageElf;
  }

  std::string ext = filepath.substr(ext_pos + 1);
  MemImageType image_type = GetMemImageTypeByName(ext);
  if (image_type == kMemImageUnknown) {
    std::ostringstream oss;
    oss << "Cannot auto-detect file type for `" << filepath << "'.";
    throw std::runtime_error(oss.str());
  }

  return image_type;
}

// Generate a single array of bytes representing the contents of PT_LOAD
// segments of the ELF file. Like objcopy, this generates a single "giant
// segment" whose first byte corresponds to the first byte of the lowest
// addressed segment and whose last byte corresponds to the last byte of the
// highest address.
static std::vector<uint8_t> FlattenElfFile(const std::string &filepath) {
  ElfFile elf(filepath);

  size_t phnum = elf.GetPhdrNum();
  const Elf32_Phdr *phdrs = elf.GetPhdrs();

  // To mimic what objcopy does (that is, the binary target of BFD), we need to
  // iterate over all loadable program headers, find the lowest address, and
  // then copy in our loadable data based on their offset with respect to the
  // found base address.

  bool any = false;
  Elf32_Addr low = 0, high = 0;
  for (size_t i = 0; i < phnum; i++) {
    const Elf32_Phdr &phdr = phdrs[i];

    if (phdr.p_type != PT_LOAD) {
      std::cout << "Program header number " << i << " in `" << filepath
                << "' is not of type PT_LOAD; ignoring." << std::endl;
      continue;
    }

    if (phdr.p_memsz == 0) {
      continue;
    }

    if (!any || phdr.p_paddr < low) {
      low = phdr.p_paddr;
    }

    Elf32_Addr seg_top = phdr.p_paddr + (phdr.p_memsz - 1);
    if (seg_top < phdr.p_paddr) {
      std::ostringstream oss;
      oss << "phdr for segment " << i << " has start 0x" << std::hex
          << phdr.p_paddr << " and size 0x" << phdr.p_memsz
          << ", which overflows the address space.";
      throw ElfError(filepath, oss.str());
    }

    if (!any || seg_top > high) {
      high = seg_top;
    }

    any = true;
  }

  // If any is false, there were no segments that contributed to the
  // file. Return nothing.
  if (!any)
    return std::vector<uint8_t>();

  // Otherwise, we know every valid byte of data has an address in the
  // range [low, high] (inclusive).
  assert(low <= high);

  size_t file_size;
  const char *file_data = elf_rawfile(elf.ptr_, &file_size);
  assert(file_data);

  StagedMem ret;

  for (size_t i = 0; i < phnum; i++) {
    const Elf32_Phdr &phdr = phdrs[i];

    if (phdr.p_type != PT_LOAD) {
      continue;
    }

    // Check the segment actually fits in the file
    if (file_size < phdr.p_offset + phdr.p_filesz) {
      std::ostringstream oss;
      oss << "phdr for segment " << i << " claims to end at offset 0x"
          << std::hex << phdr.p_offset + phdr.p_filesz
          << ", but the file only has size 0x" << file_size << ".";
      throw ElfError(filepath, oss.str());
    }

    uint32_t off = phdr.p_paddr - low;
    uint32_t dst_len = phdr.p_memsz;
    uint32_t src_len = std::min(phdr.p_filesz, dst_len);

    if (!dst_len)
      continue;

    std::vector<uint8_t> seg(dst_len, 0);
    memcpy(&seg[0], file_data + phdr.p_offset, src_len);
    ret.AddSegment(off, std::move(seg));
  }

  return ret.GetFlat();
}

// Write a "segment" of data to the given memory area.
static void WriteSegment(const MemArea &m, uint32_t offset,
                         const std::vector<uint8_t> &data) {
  assert(m.width_byte <= 32);
  assert(m.addr_loc.size == 0 || offset + data.size() <= m.addr_loc.size);
  assert((offset % m.width_byte) == 0);

  // If this fails to set scope, it will throw an error which should
  // be caught at this function's callsite.
  SVScoped scoped(m.location.data());

  // This "mini buffer" is used to transfer each write to SystemVerilog. It's
  // not massively efficient, but doing so ensures that we pass 256 bits (32
  // bytes) of initialised data each time. This is for simutil_set_mem (defined
  // in prim_util_memload.svh), whose "val" argument has SystemVerilog type bit
  // [255:0].
  uint8_t minibuf[32];
  memset(minibuf, 0, sizeof minibuf);
  assert(m.width_byte <= sizeof minibuf);

  uint32_t all_words = (data.size() + m.width_byte - 1) / m.width_byte;
  uint32_t full_data_words = data.size() / m.width_byte;
  uint32_t part_data_word_len = data.size() % m.width_byte;
  bool has_part_data_word = part_data_word_len != 0;

  uint32_t word_offset = offset / m.width_byte;

  // Copy the full data words
  for (uint32_t i = 0; i < full_data_words; ++i) {
    uint32_t dst_word = word_offset + i;
    uint32_t src_byte = i * m.width_byte;
    memcpy(minibuf, &data[src_byte], m.width_byte);
    if (!simutil_set_mem(dst_word, (svBitVecVal *)minibuf)) {
      std::ostringstream oss;
      oss << "Could not set `" << m.name << "' memory at byte offset 0x"
          << std::hex << dst_word * m.width_byte << ".";
      throw std::runtime_error(oss.str());
    }
  }

  // Copy any partial data, zeroing minibuf first to ensure that the latter
  // bytes in the word are zero.
  if (has_part_data_word) {
    memset(minibuf, 0, sizeof minibuf);
    uint32_t dst_word = word_offset + full_data_words;
    uint32_t src_byte = full_data_words * m.width_byte;
    memcpy(minibuf, &data[src_byte], part_data_word_len);
    if (!simutil_set_mem(dst_word, (svBitVecVal *)minibuf)) {
      std::ostringstream oss;
      oss << "Could not set `" << m.name << "' memory at byte offset 0x"
          << std::hex << dst_word * m.width_byte << " (partial data word).";
      throw std::runtime_error(oss.str());
    }
  }
}

static void WriteElfToMem(const MemArea &m, const std::string &filepath) {
  WriteSegment(m, 0, FlattenElfFile(filepath));
}

static void WriteVmemToMem(const MemArea &m, const std::string &filepath) {
  SVScoped scoped(m.location.data());
  // TODO: Add error handling.
  simutil_memload(filepath.data());
}

// Merge seg0 and seg1, overwriting any overlapping data in seg0 with
// that from seg1. rng0/rng1 is the base and top address of seg0/seg1,
// respectively.
static std::vector<uint8_t> MergeSegments(const AddrRange<uint32_t> &rng0,
                                          std::vector<uint8_t> &&seg0,
                                          const AddrRange<uint32_t> &rng1,
                                          std::vector<uint8_t> &&seg1) {
  // First, deal with the special case where seg1 completely contains
  // seg0 (since there's no copying needed at all).
  if (rng1.lo <= rng0.lo && rng0.hi <= rng1.hi) {
    return std::move(seg1);
  }

  uint32_t new_bot = std::min(rng0.lo, rng1.lo);
  uint32_t new_top = std::max(rng0.hi, rng1.hi);
  assert(new_bot <= new_top);
  size_t new_len = 1 + (size_t)(new_top - new_bot);
  assert(seg0.size() <= new_len);
  assert(seg1.size() <= new_len);

  // We want to avoid copying if possible. The next most efficient
  // case (after just returning seg1) is when seg0 doesn't stick out
  // the left hand end. In this case, we can extend seg1 to the right
  // (which might not cause a copy) and then copy just the bytes we
  // need from seg0.
  if (rng1.lo <= rng0.lo) {
    assert(rng1.hi < rng0.hi);
    assert(new_len == seg1.size() + (rng0.hi - rng1.hi));

    size_t old_len = seg1.size();
    std::vector<uint8_t> ret = std::move(seg1);
    ret.resize(new_len);

    // We know that that rng0 isn't completely contained in rng1 and
    // that rng0 doesn't stick out of the left hand end. That means it
    // must stick out of the right (so rng1.hi < rng0.hi). However, we
    // also know that the two ranges overlap, so rng0.lo <= rng1.hi.
    assert(rng0.lo <= rng1.hi);

    // src_off is the index of the first byte that needs copying from
    // seg0. Note that this is always at least 1 (because there is an
    // actual overlap).
    uint32_t src_off = 1 + (rng1.hi - rng0.lo);

    assert(seg0.size() == src_off + (rng0.hi - rng1.hi));

    memcpy(&ret[old_len], &seg0[src_off], rng0.hi - rng1.hi);
    return ret;
  }

  // In this final case, seg0 sticks out the left hand end. That means
  // we'll have to copy seg1 whatever happens (because we have to
  // shuffle its elements to the right). Work by resizing seg0 and
  // then writing seg1 where it's needed.
  std::vector<uint8_t> ret = std::move(seg0);
  ret.resize(new_len);

  uint32_t off = rng1.lo - rng0.lo;
  memcpy(&ret[off], &seg1[0], seg1.size());
  return ret;
}

void StagedMem::AddSegment(uint32_t offset, std::vector<uint8_t> &&seg) {
  if (seg.empty())
    return;

  uint32_t seg_top = offset + seg.size() - 1;
  assert(seg_top >= offset);

  min_addr_ = std::min(min_addr_, offset);
  max_addr_ = std::max(max_addr_, seg_top);
  segs_.Emplace(offset, seg_top, std::move(seg), MergeSegments);
}

std::vector<uint8_t> StagedMem::GetFlat() const {
  // Since max_addr_ and min_addr_ are inclusive, the size to allocate
  // is 1+(max-min). We cast to size_t to make sure the +1 doesn't
  // overflow.
  size_t len = (size_t)1 + (max_addr_ - min_addr_);
  std::vector<uint8_t> ret(len, 0);

  for (const auto &pr : segs_) {
    const AddrRange<uint32_t> &rng = pr.first;
    const std::vector<uint8_t> &seg = pr.second;
    assert(seg.size() == 1 + (rng.hi - rng.lo));
    assert(min_addr_ <= rng.lo);

    uint32_t off = rng.lo - min_addr_;
    assert(off + seg.size() <= ret.size());

    memcpy(&ret[off], &seg[0], seg.size());
  }
  return ret;
}

bool DpiMemUtil::RegisterMemoryArea(const std::string name,
                                    const std::string location) {
  // Default to 32bit width and no address
  return RegisterMemoryArea(name, location, 32, nullptr);
}

bool DpiMemUtil::RegisterMemoryArea(const std::string name,
                                    const std::string location,
                                    size_t width_bit,
                                    const MemAreaLoc *addr_loc) {
  assert((width_bit <= 256) &&
         "TODO: Memory loading only supported up to 256 bits.");
  assert(width_bit % 8 == 0);

  // First, create and register the memory by name
  MemArea mem = {.name = name,
                 .location = location,
                 .width_byte = (uint32_t)width_bit / 8,
                 .addr_loc = {.base = 0, .size = 0}};
  auto ret = name_to_mem_.emplace(name, mem);
  if (ret.second == false) {
    std::cerr << "ERROR: Can not register \"" << name << "\" at: \"" << location
              << "\" (Previously defined at: \"" << ret.first->second.location
              << "\")" << std::endl;
    return false;
  }

  MemArea *stored_mem_area = &ret.first->second;

  // If we have no address information, there's nothing more to do. However, if
  // we do have address information, we should add an entry to addr_to_mem_.
  if (!addr_loc) {
    return true;
  }

  // Check that the size of the new area is positive, and that we don't overflow
  // the address space.
  if (addr_loc->size == 0) {
    std::cerr << "ERROR: Can not register '" << name
              << "' because it has zero size.\n";
    return false;
  }
  uint32_t addr_top = addr_loc->base + (addr_loc->size - 1);
  if (addr_top < addr_loc->base) {
    std::cerr << "ERROR: Can not register '" << name
              << "' because it overflows the top of the address space.\n";
    return false;
  }

  auto clash = addr_to_mem_.EmplaceDisjoint(addr_loc->base, addr_top,
                                            std::move(stored_mem_area));
  if (clash) {
    assert(*clash);
    std::cerr << "ERROR: Can not register '" << name
              << "' because its address range overlaps the existing area `"
              << (*clash)->name << "'.\n";
    return false;
  }
  stored_mem_area->addr_loc = *addr_loc;
  return true;
}

MemImageType DpiMemUtil::GetMemImageType(const std::string &path,
                                         const char *type) {
  return type ? GetMemImageTypeByName(type) : DetectMemImageType(path);
}

void DpiMemUtil::PrintMemRegions() const {
  std::cout << "Registered memory regions:" << std::endl;
  for (const auto &pr : name_to_mem_) {
    const MemArea &m = pr.second;
    std::cout << "\t'" << m.name << "' (" << m.width_byte * 8
              << "bits) at location: '" << m.location << "'";
    if (m.addr_loc.size) {
      uint32_t low = m.addr_loc.base;
      uint32_t high = m.addr_loc.base + m.addr_loc.size - 1;
      std::cout << " (LMA range [0x" << std::hex << low << ", 0x" << high
                << "])" << std::dec;
    }
    std::cout << std::endl;
  }
}

void DpiMemUtil::LoadFileToNamedMem(bool verbose, const std::string &name,
                                    const std::string &filepath,
                                    MemImageType type) {
  // If the image type isn't specified, try to figure it out from the file name
  if (type == kMemImageUnknown) {
    type = DetectMemImageType(filepath);
  }
  assert(type != kMemImageUnknown);

  // Search for corresponding registered memory based on the name
  auto it = name_to_mem_.find(name);
  if (it == name_to_mem_.end()) {
    std::ostringstream oss;
    oss << "`" << name
        << ("' is not the name of a known memory region. "
            "Run with --meminit=list to get a list.");
    throw std::runtime_error(oss.str());
  }

  if (verbose) {
    std::cout << "Loading data from file `" << filepath << "' into memory `"
              << name << "'." << std::endl;
  }

  const MemArea &m = it->second;

  try {
    switch (type) {
      case kMemImageElf:
        WriteElfToMem(m, filepath);
        break;
      case kMemImageVmem:
        WriteVmemToMem(m, filepath);
        break;
      default:
        assert(0);
    }
  } catch (const SVScoped::Error &err) {
    std::ostringstream oss;
    oss << "No memory found at `" << err.scope_name_
        << "' (the scope associated with region `" << m.name << "').";
    throw std::runtime_error(oss.str());
  }
}

void DpiMemUtil::LoadElfToMemories(bool verbose, const std::string &filepath) {
  // Load the contents of the ELF file into the staging area
  StageElf(verbose, filepath);

  for (const auto &pr : staging_area_) {
    const std::string &mem_name = pr.first;
    const StagedMem &staged_mem = pr.second;

    auto mem_area_it = name_to_mem_.find(mem_name);
    assert(mem_area_it != name_to_mem_.end());

    const MemArea &mem_area = mem_area_it->second;

    for (const auto seg_pr : staged_mem.GetSegs()) {
      const AddrRange<uint32_t> &seg_rng = seg_pr.first;
      const std::vector<uint8_t> &seg_data = seg_pr.second;
      try {
        WriteSegment(mem_area, seg_rng.lo, seg_data);
      } catch (const SVScoped::Error &err) {
        std::ostringstream oss;
        oss << "No memory found at `" << err.scope_name_
            << "' (the scope associated with region `" << mem_area.name
            << "', used by a segment that starts at LMA 0x" << std::hex
            << mem_area.addr_loc.base + seg_rng.lo << ").";
        throw std::runtime_error(oss.str());
      }
    }
  }
}

void DpiMemUtil::StageElf(bool verbose, const std::string &path) {
  // Clear out anything that was in the staging area before
  staging_area_.clear();

  ElfFile elf(path);

  size_t file_size;
  const char *file_data = elf_rawfile(elf.ptr_, &file_size);
  assert(file_data);

  size_t phnum = elf.GetPhdrNum();
  const Elf32_Phdr *phdrs = elf.GetPhdrs();

  for (size_t i = 0; i < phnum; ++i) {
    const Elf32_Phdr &phdr = phdrs[i];
    if (phdr.p_type != PT_LOAD)
      continue;

    if (phdr.p_memsz == 0)
      continue;

    const MemArea &mem_area =
        GetRegionForSegment(path, i, phdr.p_paddr, phdr.p_memsz);

    // Check that the segment is aligned correctly for the memory
    uint32_t local_base = phdr.p_paddr - mem_area.addr_loc.base;
    if (local_base % mem_area.width_byte) {
      std::ostringstream oss;
      oss << "Segment " << i << " has LMA 0x" << std::hex << phdr.p_paddr
          << ", which starts at offset 0x" << local_base
          << " in the memory region `" << mem_area.name
          << "'. This offset is not aligned to the region's word width of "
          << std::dec << 8 * mem_area.width_byte << " bits.";
      throw ElfError(path, oss.str());
    }

    // Where does the segment finish in the file image? We don't need
    // to worry about overflow here, because we're adding two
    // uint32_t's into a size_t. But we do need to check the segment
    // actually fits in the file
    size_t off_end = (size_t)phdr.p_offset + phdr.p_filesz;
    if (file_size < off_end) {
      std::ostringstream oss;
      oss << "phdr for segment " << i << " claims to end at offset 0x"
          << std::hex << off_end - 1 << ", but the file only has size 0x"
          << file_size << ".";
      throw ElfError(path, oss.str());
    }

    if (verbose) {
      std::cout << "Loading segment " << i << " from ELF file `" << path
                << "' into memory `" << mem_area.name << "'." << std::endl;
    }

    // Get the StagedMem object associated with this memory area. If
    // there isn't one, make a new empty one.
    StagedMem &staged_mem = staging_area_[mem_area.name];

    const char *seg_data = file_data + phdr.p_offset;
    std::vector<uint8_t> vec(phdr.p_memsz, 0);
    memcpy(&vec[0], seg_data, std::min(phdr.p_filesz, phdr.p_memsz));

    staged_mem.AddSegment(local_base, std::move(vec));
  }
}

const StagedMem &DpiMemUtil::GetMemoryData(const std::string &mem_name) const {
  auto it = staging_area_.find(mem_name);
  return (it == staging_area_.end()) ? empty_ : it->second;
}

const MemArea &DpiMemUtil::GetRegionForSegment(const std::string &path,
                                               int seg_idx, uint32_t lma,
                                               uint32_t mem_sz) const {
  assert(mem_sz > 0);

  auto mem_area_it = addr_to_mem_.find(lma);
  if (mem_area_it == addr_to_mem_.end()) {
    std::ostringstream oss;
    oss << "No memory region is registered that contains the address 0x"
        << std::hex << lma << " (the base address of segment " << seg_idx
        << ").";
    throw ElfError(path, oss.str());
  }
  const MemArea *mem_area = mem_area_it->second;
  assert(mem_area);
  assert(mem_area->addr_loc.base <= lma);

  uint32_t lma_top = lma + (mem_sz - 1);
  if (lma_top < lma) {
    std::ostringstream oss;
    oss << "Integer overflow for top address of segment " << seg_idx << ".";
    throw ElfError(path, oss.str());
  }

  uint32_t local_base = lma - mem_area->addr_loc.base;
  uint32_t local_top = lma_top - mem_area->addr_loc.base;

  if (mem_area->addr_loc.size <= local_top) {
    std::ostringstream oss;
    oss << "Segment " << seg_idx << " has size 0x" << std::hex << mem_sz
        << " bytes. Its LMA of 0x" << lma << " is at offset 0x" << local_base
        << " in the memory region `" << mem_area->name
        << "', so the segment finishes at offset 0x" << local_top
        << ", but the memory region is only 0x" << mem_area->addr_loc.size
        << " bytes long.";
    throw ElfError(path, oss.str());
  }

  return *mem_area;
}
