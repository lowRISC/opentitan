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
//
// The data for any intermediate addresses that don't appear in a segment are
// set to zero.
static std::vector<uint8_t> FlattenElfFile(const std::string &filepath) {
  (void)elf_errno();
  if (elf_version(EV_CURRENT) == EV_NONE) {
    throw std::runtime_error(elf_errmsg(-1));
  }

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

    if (!any || phdr.p_paddr + phdr.p_memsz > high) {
      high = phdr.p_paddr + phdr.p_memsz;
    }

    any = true;
  }

  assert(low <= high);
  size_t len_bytes = high - low;

  size_t file_size;
  const char *file_data = elf_rawfile(elf.ptr_, &file_size);
  assert(file_data);

  std::vector<uint8_t> buf(len_bytes);
  for (size_t i = 0; i < phnum; i++) {
    const Elf32_Phdr &phdr = phdrs[i];

    if (phdr.p_type != PT_LOAD || phdr.p_filesz == 0) {
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

    // Actually copy the data across. We have just checked that there are
    // p_filesz bytes of data available, and the loop that picked low/high
    // above ensured that we have space to store for p_memsz bytes: use the
    // smaller of the two numbers.
    memcpy(&buf[phdr.p_paddr - low], file_data + phdr.p_offset,
           std::min(phdr.p_filesz, phdr.p_memsz));
  }

  return buf;
}

// Write a "segment" of data to the given memory area. Reads file_sz bytes from
// data. If mem_sz > file_sz, appends mem_sz - file_sz bytes of zeros to the
// end.
static void WriteSegment(const MemArea &m, uint32_t offset, uint32_t file_sz,
                         uint32_t mem_sz, const uint8_t *data) {
  assert(m.width_byte <= 32);
  assert(m.addr_loc.size == 0 || mem_sz + offset <= m.addr_loc.size);
  assert((offset % m.width_byte) == 0);

  // Valid ELF files probably have file_sz <= mem_sz, but it sort of makes sense
  // even if not: we are just reading the initial portion of some data stored in
  // the file.
  file_sz = std::min(file_sz, mem_sz);

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

  uint32_t all_words = (mem_sz + m.width_byte - 1) / m.width_byte;
  uint32_t full_data_words = file_sz / m.width_byte;
  uint32_t part_data_word_len = file_sz % m.width_byte;
  bool has_part_data_word = part_data_word_len != 0;
  uint32_t all_data_words = full_data_words + (has_part_data_word ? 1 : 0);

  assert(all_data_words <= all_words);
  uint32_t zero_words = all_words - all_data_words;

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

  // Zero minibuf again and splat any remaining words.
  if (zero_words > 0) {
    memset(minibuf, 0, sizeof minibuf);
    for (uint32_t i = 0; i < zero_words; ++i) {
      uint32_t dst_word = word_offset + full_data_words + i;
      if (!simutil_set_mem(dst_word, (svBitVecVal *)minibuf)) {
        std::ostringstream oss;
        oss << "Could not set `" << m.name << "' memory at byte offset 0x"
            << std::hex << dst_word * m.width_byte << " (zero word).";
        throw std::runtime_error(oss.str());
      }
    }
  }
}

static void WriteElfToMem(const MemArea &m, const std::string &filepath) {
  std::vector<uint8_t> elf_data = FlattenElfFile(filepath);
  WriteSegment(m, 0, elf_data.size(), elf_data.size(), &elf_data[0]);
}

static void WriteVmemToMem(const MemArea &m, const std::string &filepath) {
  SVScoped scoped(m.location.data());
  // TODO: Add error handling.
  simutil_memload(filepath.data());
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
  (void)elf_errno();
  if (elf_version(EV_CURRENT) == EV_NONE) {
    throw std::runtime_error(elf_errmsg(-1));
  }

  ElfFile elf(filepath);

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

    auto mem_area_it = addr_to_mem_.find(phdr.p_paddr);
    if (mem_area_it == addr_to_mem_.end()) {
      std::ostringstream oss;
      oss << "No memory region is registered that contains the address 0x"
          << std::hex << phdr.p_paddr << " (the base address of segment " << i
          << ").";
      throw ElfError(filepath, oss.str());
    }
    const MemArea &mem_area = *mem_area_it->second;
    assert(mem_area.addr_loc.base <= phdr.p_paddr);

    uint32_t lma_top = phdr.p_paddr + (phdr.p_memsz - 1);
    uint32_t off_end = phdr.p_offset + phdr.p_filesz;

    // Overflow checks
    if (lma_top < phdr.p_paddr) {
      std::ostringstream oss;
      oss << "Integer overflow for top address of segment " << i << ".";
      throw ElfError(filepath, oss.str());
    }
    if (off_end < phdr.p_offset) {
      std::ostringstream oss;
      oss << "Integer overflow for top file offset of segment " << i << ".";
      throw ElfError(filepath, oss.str());
    }

    uint32_t local_base = phdr.p_paddr - mem_area.addr_loc.base;
    uint32_t local_top = lma_top - mem_area.addr_loc.base;

    if (mem_area.addr_loc.size <= local_top) {
      std::ostringstream oss;
      oss << "Segment " << i << " has size 0x" << std::hex << phdr.p_memsz
          << " bytes. Its LMA of 0x" << phdr.p_paddr << " is at offset 0x"
          << local_base << " in the memory region `" << mem_area.name
          << "', so the segment finishes at offset 0x" << local_top
          << ", but the memory region is only 0x" << mem_area.addr_loc.size
          << " bytes long.";
      throw ElfError(filepath, oss.str());
    }

    // Check that the segment is aligned correctly for the memory
    if (local_base % mem_area.width_byte) {
      std::ostringstream oss;
      oss << "Segment " << i << " has LMA 0x" << std::hex << phdr.p_paddr
          << ", which starts at offset 0x" << local_base
          << " in the memory region `" << mem_area.name
          << "'. This offset is not aligned to the region's word width of "
          << std::dec << 8 * mem_area.width_byte << " bits.";
      throw ElfError(filepath, oss.str());
    }

    // Check the segment actually fits in the file
    if (file_size < off_end) {
      std::ostringstream oss;
      oss << "phdr for segment " << i << " claims to end at offset 0x"
          << std::hex << off_end - 1 << ", but the file only has size 0x"
          << file_size << ".";
      throw ElfError(filepath, oss.str());
    }

    if (verbose) {
      std::cout << "Loading segment " << i << " from ELF file `" << filepath
                << "' into memory `" << mem_area.name << "'." << std::endl;
    }

    const char *seg_data = file_data + phdr.p_offset;
    try {
      WriteSegment(mem_area, local_base, phdr.p_filesz, phdr.p_memsz,
                   (const uint8_t *)seg_data);
    } catch (const SVScoped::Error &err) {
      std::ostringstream oss;
      oss << "No memory found at `" << err.scope_name_
          << "' (the scope associated with region `" << mem_area.name
          << "', used by segment " << i << ", which starts at LMA 0x"
          << std::hex << phdr.p_paddr << ").";
      throw std::runtime_error(oss.str());
    }
  }
}
