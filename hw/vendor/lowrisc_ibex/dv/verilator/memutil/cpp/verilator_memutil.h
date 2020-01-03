// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef VERILATOR_MEMUTIL_H_
#define VERILATOR_MEMUTIL_H_

#include "sim_ctrl_extension.h"

#include <vltstd/svdpi.h>

#include <map>
#include <string>

enum MemImageType {
  kMemImageUnknown = 0,
  kMemImageElf,
  kMemImageVmem,
};

struct MemArea {
  std::string name;      // Unique identifier
  std::string location;  // Design scope location
};

/**
 * Provide various memory loading utilities for Verilator simulations
 *
 * These utilities require the corresponding DPI functions:
 * simutil_verilator_memload()
 * simutil_verilator_set_mem()
 * to be defined somewhere as SystemVerilog functions.
 */
class VerilatorMemUtil : public SimCtrlExtension {
 public:
  /**
   * Register a memory as instantiated by generic ram
   *
   * The |name| must be a unique identifier. The function will return false
   * if |name| is already used. |location| is the path to the scope of the
   * instantiated memory, which needs to support the DPI-C interfaces
   * 'simutil_verilator_memload' and 'simutil_verilator_set_mem' used for
   * 'vmem' and 'elf' files, respectively.
   *
   * Memories must be registered before command arguments are parsed by
   * ParseCommandArgs() in order for them to be known.
   */
  bool RegisterMemoryArea(const std::string name, const std::string location);

  /**
   * Parse command line arguments
   *
   * Process all recognized command-line arguments from argc/argv.
   *
   * @param argc, argv Standard C command line arguments
   * @param exit_app Indicate that program should terminate
   * @return Return code, true == success
   */
  virtual bool ParseCLIArguments(int argc, char **argv, bool &exit_app);

 private:
  std::map<std::string, MemArea> mem_register_;

  /**
   * Print a list of all registered memory regions
   *
   * @see RegisterMemoryArea()
   */
  void PrintMemRegions() const;

  /**
   * Print help how to use this tool
   */
  void PrintHelp() const;

  /**
   * Parse argument section specific to memory initialization.
   *
   * Must be in the form of: name,file[,type].
   */
  bool ParseMemArg(std::string mem_argument, std::string &name,
                   std::string &filepath, MemImageType &type);

  MemImageType DetectMemImageType(const std::string filepath);

  MemImageType GetMemImageTypeByName(const std::string name);

  bool IsFileReadable(std::string filepath) const;

  /**
   * Dump an ELF file into a raw binary
   */
  bool ElfFileToBinary(const std::string &filepath, uint8_t **data,
                       size_t &len_bytes) const;

  bool MemWrite(const std::string &name, const std::string &filepath);
  bool MemWrite(const std::string &name, const std::string &filepath,
                MemImageType type);
  bool MemWrite(const MemArea &m, const std::string &filepath,
                MemImageType type);
  bool WriteElfToMem(const svScope &scope, const std::string &filepath);
  bool WriteVmemToMem(const svScope &scope, const std::string &filepath);
};

#endif  // VERILATOR_MEMUTIL_H_
