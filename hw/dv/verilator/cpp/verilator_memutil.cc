// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "verilator_memutil.h"

#include <cassert>
#include <cstring>
#include <fcntl.h>
#include <getopt.h>
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
extern void simutil_verilator_memload(const char *file);

/**
 * Write a 32 bit word |val| to memory at index |index|
 *
 * @return 1 if successful, 0 otherwise
 */
extern int simutil_verilator_set_mem(int index, const svBitVecVal *val);
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

// Print a usage message to stdout
static void PrintHelp() {
  std::cout << "Simulation memory utilities:\n\n"
               "-r|--rominit=FILE\n"
               "  Initialize the ROM with FILE (elf/vmem)\n\n"
               "-m|--raminit=FILE\n"
               "  Initialize the RAM with FILE (elf/vmem)\n\n"
               "-f|--flashinit=FILE\n"
               "  Initialize the FLASH with FILE (elf/vmem)\n\n"
               "-l|--meminit=NAME,FILE[,TYPE]\n"
               "  Initialize memory region NAME with FILE [of TYPE]\n"
               "  TYPE is either 'elf' or 'vmem'\n\n"
               "-E|--load-elf=FILE\n"
               "  Load ELF file, using segment LMAs to pick memory regions\n\n"
               "-l list|--meminit=list\n"
               "  Print registered memory regions\n\n"
               "--verbose-mem-load\n"
               "  Print a message for each memory load\n\n"
               "-h|--help\n"
               "  Show help\n\n";
}

// Convert a string to a MemImageType, returning kMemImageUnknown if it's not a
// known name.
static MemImageType GetMemImageTypeByName(const std::string &name) {
  if (name == "elf")
    return kMemImageElf;
  if (name == "vmem")
    return kMemImageVmem;
  return kMemImageUnknown;
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

namespace {
// An instruction to load the file at filepath to the memory called name. If
// name is the empty string then type must be kMemImageElf and this is an
// instruction to load an ELF file, picking memories by LMA.
struct LoadArg {
  std::string name;
  std::string filepath;
  MemImageType type;
};
}  // namespace

// Parse a meminit command-line argument. This should be of the form
// mem_area,file[,type]. Throw a std::runtime_error if something looks wrong.
static LoadArg ParseMemArg(std::string mem_argument) {
  std::array<std::string, 3> args;
  size_t pos = 0;
  size_t end_pos = 0;
  size_t i;

  for (i = 0; i < 3; ++i) {
    end_pos = mem_argument.find(",", pos);
    // Check for possible exit conditions
    if (pos == end_pos) {
      std::ostringstream oss;
      oss << "empty field in: `" << mem_argument << "'.";
      throw std::runtime_error(oss.str());
    }
    if (end_pos == std::string::npos) {
      args[i] = mem_argument.substr(pos);
      break;
    }
    args[i] = mem_argument.substr(pos, end_pos - pos);
    pos = end_pos + 1;
  }
  // mem_argument is not empty as getopt requires an argument,
  // but not a valid argument for memory initialization
  if (i == 0) {
    std::ostringstream oss;
    oss << "meminit must be in the format `name,file[,type]'. Got: `"
        << mem_argument << "'.";
    throw std::runtime_error(oss.str());
  }

  MemImageType type;
  if (i == 1) {
    // Type not set explicitly
    type = DetectMemImageType(args[1]);
  } else {
    type = GetMemImageTypeByName(args[2]);
  }

  return {.name = args[0], .filepath = args[1], .type = type};
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

  svScope scope = svGetScopeFromName(m.location.data());
  if (!scope) {
    std::ostringstream oss;
    oss << "No memory found at `" << m.location
        << "' (the scope associated with region `" << m.name << "').";
    throw std::runtime_error(oss.str());
  }

  SVScoped scoped(scope);

  // This "mini buffer" is used to transfer each write to SystemVerilog. It's
  // not massively efficient, but doing so ensures that we pass 256 bits (32
  // bytes) of initialised data each time. This is for simutil_verilator_set_mem
  // (defined in prim_util_memload.svh), whose "val" argument has SystemVerilog
  // type bit [255:0].
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
    if (!simutil_verilator_set_mem(dst_word, (svBitVecVal *)minibuf)) {
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
    if (!simutil_verilator_set_mem(dst_word, (svBitVecVal *)minibuf)) {
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
      if (!simutil_verilator_set_mem(dst_word, (svBitVecVal *)minibuf)) {
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
  svScope scope = svGetScopeFromName(m.location.data());
  if (!scope) {
    std::ostringstream oss;
    oss << "No memory found at `" << m.location
        << "' (the scope associated with region `" << m.name << "').";
    throw std::runtime_error(oss.str());
  }

  SVScoped scoped(scope);
  // TODO: Add error handling.
  simutil_verilator_memload(filepath.data());
}

bool VerilatorMemUtil::RegisterMemoryArea(const std::string name,
                                          const std::string location) {
  // Default to 32bit width and no address
  return RegisterMemoryArea(name, location, 32, nullptr);
}

bool VerilatorMemUtil::RegisterMemoryArea(const std::string name,
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

  // If the existing map is non-empty, we must check for overlaps
  if (!addr_to_mem_.empty()) {
    // We start by checking for an overlap "from the right". This would be a
    // region that starts strictly above addr_loc->base, but where it's low
    // address is still less than addr_top. We can use std::map::upper_bound to
    // find the first region strictly above addr_loc->base (which returns the
    // end iterator if there isn't one).
    auto right_it = addr_to_mem_.upper_bound(addr_loc->base);
    if (right_it != addr_to_mem_.end()) {
      const MemAreaLoc &ub_loc = right_it->second->addr_loc;
      assert(ub_loc.size != 0);
      if (ub_loc.base <= addr_top) {
        std::cerr << "ERROR: Can not register '" << name
                  << "' because its address range overlaps to left of '"
                  << right_it->second->name << "'.\n";
        return false;
      }
    }

    // We also need to check from the other side. This would be a region that
    // starts at or before addr_loc->base and extends past it. If right_it is
    // addr_to_mem_.begin(), there is no such region (because the lowest
    // addressed region already starts above addr_loc->base). Otherwise,
    // decrement right_it to get the highest addressed region that starts at or
    // before addr_loc->base. Note this still works if right_it is the end
    // iterator: we just pick up the last region, which we know exists because
    // addr_to_mem_ is not empty.
    if (right_it != addr_to_mem_.begin()) {
      auto left_it = std::prev(right_it);
      const MemAreaLoc &lb_loc = left_it->second->addr_loc;
      assert(lb_loc.size != 0);
      uint32_t lb_max = lb_loc.base + lb_loc.size;
      if (addr_loc->base <= lb_max) {
        std::cerr << "ERROR: Can not register '" << name
                  << "' because its address range overlaps to right of '"
                  << left_it->second->name << "'.\n";
        return false;
      }
    }
  }

  // Phew, no overlap!
  addr_to_mem_.insert(std::make_pair(addr_loc->base, stored_mem_area));
  stored_mem_area->addr_loc = *addr_loc;
  return true;
}

bool VerilatorMemUtil::ParseCLIArguments(int argc, char **argv,
                                         bool &exit_app) {
  const struct option long_options[] = {
      {"rominit", required_argument, nullptr, 'r'},
      {"raminit", required_argument, nullptr, 'm'},
      {"flashinit", required_argument, nullptr, 'f'},
      {"meminit", required_argument, nullptr, 'l'},
      {"verbose-mem-load", no_argument, nullptr, 'V'},
      {"load-elf", required_argument, nullptr, 'E'},
      {"help", no_argument, nullptr, 'h'},
      {nullptr, no_argument, nullptr, 0}};

  std::vector<LoadArg> load_args;
  bool verbose = false;

  // Reset the command parsing index in-case other utils have already parsed
  // some arguments
  optind = 1;
  while (1) {
    int c = getopt_long(argc, argv, ":r:m:f:l:E:h", long_options, nullptr);
    if (c == -1) {
      break;
    }

    // Disable error reporting by getopt
    opterr = 0;

    switch (c) {
      case 0:
        break;
      case 'r':
        load_args.push_back(
            {.name = "rom", .filepath = optarg, .type = kMemImageUnknown});
        break;
      case 'm':
        load_args.push_back(
            {.name = "ram", .filepath = optarg, .type = kMemImageUnknown});
        break;
      case 'f':
        load_args.push_back(
            {.name = "flash", .filepath = optarg, .type = kMemImageUnknown});
        break;
      case 'l':
        if (strcasecmp(optarg, "list") == 0) {
          PrintMemRegions();
          exit_app = true;
          return true;
        }

        // --meminit / -l
        try {
          load_args.emplace_back(ParseMemArg(optarg));
        } catch (const std::runtime_error &err) {
          std::cerr << "ERROR: " << err.what() << std::endl;
          return false;
        }
        break;
      case 'V':
        verbose = true;
        break;
      case 'E':
        load_args.push_back(
            {.name = "", .filepath = optarg, .type = kMemImageElf});
        break;
      case 'h':
        PrintHelp();
        return true;
      case ':':  // missing argument
        std::cerr << "ERROR: Missing argument." << std::endl << std::endl;
        return false;
      case '?':
      default:;
        // Ignore unrecognized options since they might be consumed by
        // other utils
    }
  }

  for (const LoadArg &arg : load_args) {
    try {
      if (!arg.name.empty()) {
        LoadFileToNamedMem(verbose, arg.name, arg.filepath, arg.type);
      } else {
        assert(arg.type == kMemImageElf);
        LoadElfToMemories(verbose, arg.filepath);
      }
    } catch (const std::exception &err) {
      std::cerr << "ERROR: " << err.what() << std::endl;
      return false;
    }
  }

  return true;
}

void VerilatorMemUtil::PrintMemRegions() const {
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

void VerilatorMemUtil::LoadFileToNamedMem(bool verbose, const std::string &name,
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
    oss << "`" << name << ("' is not the name of a known memory region. "
                           "Run with --meminit=list to get a list.");
    throw std::runtime_error(oss.str());
  }

  if (verbose) {
    std::cout << "Loading data from file `" << filepath << "' into memory `"
              << name << "'." << std::endl;
  }

  const MemArea &m = it->second;

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
}

void VerilatorMemUtil::LoadElfToMemories(bool verbose,
                                         const std::string &filepath) {
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

    const MemArea *mem_area = FindRegionForAddr(phdr.p_paddr);
    if (!mem_area) {
      std::ostringstream oss;
      oss << "No memory region is registered that contains the address 0x"
          << std::hex << phdr.p_paddr << " (the base address of segment " << i
          << ").";
      throw ElfError(filepath, oss.str());
    }
    assert(mem_area->addr_loc.base <= phdr.p_paddr);

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

    uint32_t local_base = phdr.p_paddr - mem_area->addr_loc.base;
    uint32_t local_top = lma_top - mem_area->addr_loc.base;

    if (mem_area->addr_loc.size <= local_top) {
      std::ostringstream oss;
      oss << "Segment " << i << " has size 0x" << std::hex << phdr.p_memsz
          << " bytes. Its LMA of 0x" << phdr.p_paddr << " is at offset 0x"
          << local_base << " in the memory region `" << mem_area->name
          << "', so the segment finishes at offset 0x" << local_top
          << ", but the memory region is only 0x" << mem_area->addr_loc.size
          << " bytes long.";
      throw ElfError(filepath, oss.str());
    }

    // Check that the segment is aligned correctly for the memory
    if (local_base % mem_area->width_byte) {
      std::ostringstream oss;
      oss << "Segment " << i << " has LMA 0x" << std::hex << phdr.p_paddr
          << ", which starts at offset 0x" << local_base
          << " in the memory region `" << mem_area->name
          << "'. This offset is not aligned to the region's word width of "
          << std::dec << 8 * mem_area->width_byte << " bits.";
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
                << "' into memory `" << mem_area->name << "'." << std::endl;
    }

    const char *seg_data = file_data + phdr.p_offset;
    WriteSegment(*mem_area, local_base, phdr.p_filesz, phdr.p_memsz,
                 (const uint8_t *)seg_data);
  }
}

const MemArea *VerilatorMemUtil::FindRegionForAddr(uint32_t lma) const {
  // To find the memory area containing lma, use upper_bound to find the first
  // region strictly after it, and then std::prev to step backwards. This fails
  // if either the map is empty (obviously!) or if ub_it is already the
  // beginning of the map.
  if (addr_to_mem_.empty())
    return nullptr;

  auto ub_it = addr_to_mem_.upper_bound(lma);
  if (ub_it == addr_to_mem_.begin())
    return nullptr;

  const MemArea *m = std::prev(ub_it)->second;

  // Every entry in addr_to_mem_ should have a valid pointer to a MemArea with a
  // valid location.
  assert(m != nullptr);
  assert(m->addr_loc.size != 0);

  // What's more, the base of the location should be less than equal to lma
  // (because it's strictly less than the smallest entry strictly greater).
  assert(m->addr_loc.base <= lma);

  // This means that we've found the right region iff the top of the region
  // includes lma.
  uint32_t addr_top = m->addr_loc.base + (m->addr_loc.size - 1);
  return (lma <= addr_top) ? m : nullptr;
}
