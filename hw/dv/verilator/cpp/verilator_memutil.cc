// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "verilator_memutil.h"

#include <array>
#include <cassert>
#include <cstring>
#include <getopt.h>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

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

// Parse a meminit command-line argument and write the result to the
// mem_arg output pointer. The command-line argument should be of the
// form mem_area,file[,type].
//
// Return true on success. On failure, return false and write an error
// message to err_msg.
static bool ParseMemArg(const std::string mem_argument, LoadArg *load_arg,
                        std::string *err_msg) {
  std::array<std::string, 3> args;
  size_t pos = 0;
  size_t end_pos = 0;
  size_t i;

  assert(load_arg);
  assert(err_msg);

  for (i = 0; i < 3; ++i) {
    end_pos = mem_argument.find(",", pos);
    // Check for possible exit conditions
    if (pos == end_pos) {
      std::ostringstream oss;
      oss << "empty field in: `" << mem_argument << "'.";
      *err_msg = oss.str();
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
    std::ostringstream oss;
    oss << "meminit must be in the format `name,file[,type]'. Got: `"
        << mem_argument << "'.";
    *err_msg = oss.str();
    return false;
  }

  const char *str_type = (2 <= i) ? args[2].c_str() : nullptr;

  load_arg->name = args[0];
  load_arg->filepath = args[1];
  load_arg->type = DpiMemUtil::GetMemImageType(args[1], str_type);
  return true;
}

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

VerilatorMemUtil::VerilatorMemUtil() : allocation_(new DpiMemUtil()) {
  mem_util_ = allocation_.get();
}

VerilatorMemUtil::VerilatorMemUtil(DpiMemUtil *mem_util) : mem_util_(mem_util) {
  assert(mem_util);
}

bool VerilatorMemUtil::ParseCLIArguments(int argc, char **argv,
                                         bool &exit_app) {
  const struct option long_options[] = {
      {"rominit", required_argument, nullptr, 'r'},
      {"raminit", required_argument, nullptr, 'm'},
      {"flashinit", required_argument, nullptr, 'f'},
      {"otpinit", required_argument, nullptr, 'o'},
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
    int c = getopt_long(argc, argv, "-:r:m:f:l:E:h", long_options, nullptr);
    if (c == -1) {
      break;
    }

    // Disable error reporting by getopt
    opterr = 0;

    switch (c) {
      case 0:
      case 1:
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
      case 'o':
        load_args.push_back(
            {.name = "otp", .filepath = optarg, .type = kMemImageUnknown});
        break;
      case 'l': {
        LoadArg load_arg;
        std::string load_err_msg;

        if (strcasecmp(optarg, "list") == 0) {
          mem_util_->PrintMemRegions();
          exit_app = true;
          return true;
        }

        if (!ParseMemArg(optarg, &load_arg, &load_err_msg)) {
          std::cerr << "ERROR: " << load_err_msg << std::endl;
          return false;
        } else {
          load_args.emplace_back(load_arg);
        }
        break;
      }
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
        mem_util_->LoadFileToNamedMem(verbose, arg.name, arg.filepath,
                                      arg.type);
      } else {
        assert(arg.type == kMemImageElf);
        mem_util_->LoadElfToMemories(verbose, arg.filepath);
      }
    } catch (const std::exception &err) {
      std::cerr << "ERROR: " << err.what() << std::endl;
      return false;
    }
  }

  return true;
}
