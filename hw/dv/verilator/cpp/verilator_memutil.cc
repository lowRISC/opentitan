// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "verilator_memutil.h"

#include <fcntl.h>
#include <gelf.h>
#include <getopt.h>
#include <libelf.h>
#include <sys/stat.h>
#include <unistd.h>

#include <cassert>
#include <cstring>
#include <iostream>
#include <list>

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

bool VerilatorMemUtil::RegisterMemoryArea(const std::string name,
                                          const std::string location) {
  // Default to 32bit width
  return RegisterMemoryArea(name, location, 32);
}

bool VerilatorMemUtil::RegisterMemoryArea(const std::string name,
                                          const std::string location,
                                          size_t width_bit) {
  MemArea mem = {.name = name, .location = location, .width_bit = width_bit};

  assert((width_bit <= 256) &&
         "TODO: Memory loading only supported up to 256 bits.");

  auto ret = mem_register_.emplace(name, mem);
  if (ret.second == false) {
    std::cerr << "ERROR: Can not register \"" << name << "\" at: \"" << location
              << "\" (Previously defined at: \"" << ret.first->second.location
              << "\")" << std::endl;
    return false;
  }
  return true;
}

bool VerilatorMemUtil::ParseCLIArguments(int argc, char **argv,
                                         bool &exit_app) {
  const struct option long_options[] = {
      {"rominit", required_argument, nullptr, 'r'},
      {"raminit", required_argument, nullptr, 'm'},
      {"flashinit", required_argument, nullptr, 'f'},
      {"meminit", required_argument, nullptr, 'l'},
      {"help", no_argument, nullptr, 'h'},
      {nullptr, no_argument, nullptr, 0}};

  // Reset the command parsing index in-case other utils have already parsed
  // some arguments
  optind = 1;
  while (1) {
    int c = getopt_long(argc, argv, ":r:m:f:l:h", long_options, nullptr);
    if (c == -1) {
      break;
    }

    // Disable error reporting by getopt
    opterr = 0;

    switch (c) {
      case 0:
        break;
      case 'r':
        if (!MemWrite("rom", optarg)) {
          std::cerr << "ERROR: Unable to initialize memory." << std::endl;
          return false;
        }
        break;
      case 'm':
        if (!MemWrite("ram", optarg)) {
          std::cerr << "ERROR: Unable to initialize memory." << std::endl;
          return false;
        }
        break;
      case 'f':
        if (!MemWrite("flash", optarg)) {
          std::cerr << "ERROR: Unable to initialize memory." << std::endl;
          return false;
        }
        break;
      case 'l': {
        if (strcasecmp(optarg, "list") == 0) {
          PrintMemRegions();
          exit_app = true;
          return true;
        }

        std::string name;
        std::string filepath;
        MemImageType type;
        if (!ParseMemArg(optarg, name, filepath, type)) {
          std::cerr << "ERROR: Unable to parse meminit arguments." << std::endl;
          return false;
        }

        if (!MemWrite(name, filepath, type)) {
          std::cerr << "ERROR: Unable to initialize memory." << std::endl;
          return false;
        }
      } break;
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

  return true;
}

void VerilatorMemUtil::PrintMemRegions() const {
  std::cout << "Registered memory regions:" << std::endl;
  for (const auto &m : mem_register_) {
    std::cout << "\t'" << m.second.name << "' (" << m.second.width_bit
              << "bits) at location: '" << m.second.location << "'"
              << std::endl;
  }
}

void VerilatorMemUtil::PrintHelp() const {
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
               "-l list|--meminit=list\n"
               "  Print registered memory regions\n\n"
               "-h|--help\n"
               "  Show help\n\n";
}

bool VerilatorMemUtil::ParseMemArg(std::string mem_argument, std::string &name,
                                   std::string &filepath, MemImageType &type) {
  std::array<std::string, 3> args;
  size_t pos = 0;
  size_t end_pos = 0;
  size_t i;

  for (i = 0; i < 3; ++i) {
    end_pos = mem_argument.find(",", pos);
    // Check for possible exit conditions
    if (pos == end_pos) {
      std::cerr << "ERROR: empty field in: " << mem_argument << std::endl;
      return false;
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
    std::cerr << "ERROR: meminit must be in \"name,file[,type]\""
              << " got: " << mem_argument << std::endl;
    return false;
  }

  name = args[0];
  filepath = args[1];

  if (i == 1) {
    // Type not set explicitly
    type = DetectMemImageType(filepath);
  } else {
    type = GetMemImageTypeByName(args[2]);
  }

  return true;
}

MemImageType VerilatorMemUtil::DetectMemImageType(const std::string filepath) {
  size_t ext_pos = filepath.find_last_of(".");
  std::string ext = filepath.substr(ext_pos + 1);

  if (ext_pos == std::string::npos) {
    // Assume ELF files if no file extension is given.
    // TODO: Make this more robust by actually checking the file contents.
    return kMemImageElf;
  }
  return GetMemImageTypeByName(ext);
}

MemImageType VerilatorMemUtil::GetMemImageTypeByName(const std::string name) {
  if (name.compare("elf") == 0) {
    return kMemImageElf;
  }
  if (name.compare("vmem") == 0) {
    return kMemImageVmem;
  }
  return kMemImageUnknown;
}

bool VerilatorMemUtil::IsFileReadable(std::string filepath) const {
  struct stat statbuf;
  return stat(filepath.data(), &statbuf) == 0;
}

bool VerilatorMemUtil::ElfFileToBinary(const std::string &filepath,
                                       uint8_t **data,
                                       size_t &len_bytes) const {
  uint8_t *buf;
  bool retval, any = false;
  GElf_Phdr phdr;
  GElf_Addr high = 0;
  GElf_Addr low = (GElf_Addr)-1;
  Elf_Data *elf_data;
  size_t i;

  (void)elf_errno();
  len_bytes = 0;

  if (elf_version(EV_CURRENT) == EV_NONE) {
    std::cerr << elf_errmsg(-1) << std::endl;
    return false;
  }

  int fd = open(filepath.c_str(), O_RDONLY, 0);
  if (fd < 0) {
    std::cerr << "Could not open file: " << filepath << std::endl;
    return false;
  }

  Elf *elf_desc;
  elf_desc = elf_begin(fd, ELF_C_READ, NULL);
  if (elf_desc == NULL) {
    std::cerr << elf_errmsg(-1) << " in: " << filepath << std::endl;
    retval = false;
    goto return_fd_end;
  }
  if (elf_kind(elf_desc) != ELF_K_ELF) {
    std::cerr << "Not a ELF file: " << filepath << std::endl;
    retval = false;
    goto return_elf_end;
  }
  // TODO: add support for ELFCLASS64
  if (gelf_getclass(elf_desc) != ELFCLASS32) {
    std::cerr << "Not a 32-bit ELF file: " << filepath << std::endl;
    retval = false;
    goto return_elf_end;
  }

  size_t phnum;
  if (elf_getphdrnum(elf_desc, &phnum) != 0) {
    std::cerr << elf_errmsg(-1) << " in: " << filepath << std::endl;
    retval = false;
    goto return_elf_end;
  }

  //
  // To mimic what objcopy does (that is, the binary target of BFD), we need to
  // iterate over all loadable program headers, find the lowest address, and
  // then copy in our loadable sections based on their offset with respect to
  // the found base address.
  //
  for (i = 0; i < phnum; i++) {
    if (gelf_getphdr(elf_desc, i, &phdr) == NULL) {
      std::cerr << elf_errmsg(-1) << " segment number: " << i
                << " in: " << filepath << std::endl;
      retval = false;
      goto return_elf_end;
    }

    if (phdr.p_type != PT_LOAD) {
      std::cout << "Program header number " << i << " is not of type PT_LOAD; "
                << "ignoring." << std::endl;
      continue;
    }

    if (phdr.p_filesz == 0) {
      continue;
    }

    if (!any || phdr.p_paddr < low) {
      low = phdr.p_paddr;
    }

    if (!any || phdr.p_paddr + phdr.p_filesz > high) {
      high = phdr.p_paddr + phdr.p_filesz;
    }

    any = true;
  }

  len_bytes = high - low;
  buf = (uint8_t *)malloc(len_bytes);
  assert(buf != NULL);

  for (i = 0; i < phnum; i++) {
    (void)gelf_getphdr(elf_desc, i, &phdr);

    if (phdr.p_type != PT_LOAD || phdr.p_filesz == 0) {
      continue;
    }

    elf_data = elf_getdata_rawchunk(elf_desc, phdr.p_offset, phdr.p_filesz,
                                    ELF_T_BYTE);

    if (elf_data == NULL) {
      retval = false;
      free(buf);
      goto return_elf_end;
    }

    memcpy(&buf[phdr.p_paddr - low], (uint8_t *)elf_data->d_buf,
           elf_data->d_size);
  }

  *data = buf;
  retval = true;

return_elf_end:
  elf_end(elf_desc);
return_fd_end:
  close(fd);
  return retval;
}

bool VerilatorMemUtil::MemWrite(const std::string &name,
                                const std::string &filepath) {
  MemImageType type = DetectMemImageType(filepath);
  if (type == kMemImageUnknown) {
    std::cerr << "ERROR: Unable to detect file type for: " << filepath
              << std::endl;
    // Continuing for more error messages
  }
  return MemWrite(name, filepath, type);
}

bool VerilatorMemUtil::MemWrite(const std::string &name,
                                const std::string &filepath,
                                MemImageType type) {
  // Search for corresponding registered memory based on the name
  auto it = mem_register_.find(name);
  if (it == mem_register_.end()) {
    std::cerr << "ERROR: Memory location not set for: '" << name << "'"
              << std::endl;
    PrintMemRegions();
    return false;
  }

  if (!MemWrite(it->second, filepath, type)) {
    std::cerr << "ERROR: Setting memory '" << name << "' failed." << std::endl;
    return false;
  }
  return true;
}

bool VerilatorMemUtil::MemWrite(const MemArea &m, const std::string &filepath,
                                MemImageType type) {
  if (!IsFileReadable(filepath)) {
    std::cerr << "ERROR: Memory initialization file "
              << "'" << filepath << "'"
              << " is not readable." << std::endl;
    return false;
  }

  svScope scope = svGetScopeFromName(m.location.data());
  if (!scope) {
    std::cerr << "ERROR: No memory found at " << m.location << std::endl;
    return false;
  }

  if ((m.width_bit % 8) != 0) {
    std::cerr << "ERROR: width for: " << m.name
              << "must be a multiple of 8 (was : " << m.width_bit << ")"
              << std::endl;
    return false;
  }
  size_t size_byte = m.width_bit / 8;

  switch (type) {
    case kMemImageElf:
      if (!WriteElfToMem(scope, filepath, size_byte)) {
        std::cerr << "ERROR: Writing ELF file to memory \"" << m.name << "\" ("
                  << m.location << ") failed." << std::endl;
        return false;
      }
      break;
    case kMemImageVmem:
      if (!WriteVmemToMem(scope, filepath)) {
        std::cerr << "ERROR: Writing VMEM file to memory \"" << m.name << "\" ("
                  << m.location << ") failed." << std::endl;
        return false;
      }
      break;
    case kMemImageUnknown:
    default:
      std::cerr << "ERROR: Unknown file type for " << m.name << std::endl;
      return false;
  }
  return true;
}

bool VerilatorMemUtil::WriteElfToMem(const svScope &scope,
                                     const std::string &filepath,
                                     size_t size_byte) {
  bool retcode;
  svScope prev_scope = svSetScope(scope);

  uint8_t *buf = nullptr;
  size_t len_bytes;

  if (!ElfFileToBinary(filepath, &buf, len_bytes)) {
    std::cerr << "ERROR: Could not load: " << filepath << std::endl;
    retcode = false;
    goto ret;
  }
  for (int i = 0; i < (len_bytes + size_byte - 1) / size_byte; ++i) {
    if (!simutil_verilator_set_mem(i, (svBitVecVal *)&buf[size_byte * i])) {
      std::cerr << "ERROR: Could not set memory byte: " << i * size_byte << "/"
                << len_bytes << "" << std::endl;

      retcode = false;
      goto ret;
    }
  }

  retcode = true;

ret:
  svSetScope(prev_scope);
  free(buf);
  return retcode;
}

bool VerilatorMemUtil::WriteVmemToMem(const svScope &scope,
                                      const std::string &filepath) {
  svScope prev_scope = svSetScope(scope);

  // TODO: Add error handling.
  simutil_verilator_memload(filepath.data());

  svSetScope(prev_scope);
  return true;
}
