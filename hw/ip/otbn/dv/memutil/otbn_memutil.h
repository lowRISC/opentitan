// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#pragma once

#include <svdpi.h>

#include "dpi_memutil.h"

class OtbnMemUtil : public DpiMemUtil {
 public:
  // Constructor. top_scope is the SV scope that contains IMEM and
  // DMEM memories as u_imem and u_dmem, respectively.
  OtbnMemUtil(const std::string &top_scope);

  // Load an ELF file at the given path and backdoor load it into the
  // attached memories.
  //
  // If something goes wrong, throws a std::exception.
  void LoadElf(const std::string &elf_path);

  // Get access to the segments currently staged for imem/dmem
  const StagedMem::SegMap &GetSegs(bool is_imem) const;
};

// DPI-accessible wrappers
extern "C" {
OtbnMemUtil *OtbnMemUtilMake(const char *top_scope);
void OtbnMemUtilFree(OtbnMemUtil *mem_util);

// Loads an ELF file into memory via the backdoor. Returns 1'b1 on success.
// Prints a message to stderr and returns 1'b0 on failure.
svBit OtbnMemUtilLoadElf(OtbnMemUtil *mem_util, const char *elf_path);

// Loads an ELF file into the OtbnMemUtil object, but doesn't touch the
// simulated memory. Returns 1'b1 on success. Prints a message to stderr and
// returns 1'b0 on failure.
svBit OtbnMemUtilStageElf(OtbnMemUtil *mem_util, const char *elf_path);

// Returns the number of segments currently staged in imem/dmem.
int OtbnMemUtilGetSegCount(OtbnMemUtil *mem_util, svBit is_imem);

// Gets offset and size (both in 32-bit words) for a segment currently staged
// in imem/dmem. Both are returned with output arguments. Returns 1'b1 on
// success. Prints a message to stderr and returns 1'b0 on failure.
svBit OtbnMemUtilGetSegInfo(OtbnMemUtil *mem_util, svBit is_imem, int seg_idx,
                            /* output bit[31:0] */ svBitVecVal *seg_off,
                            /* output bit[31:0] */ svBitVecVal *seg_size);

// Gets a word of data from segments currently staged in imem/dmem. If there
// is a word at that address, the function writes its value to the output
// argument and then returns 1'b1. If there is no word at that address, the
// output argument is untouched and the function returns 1'b0.
//
// If word_off is invalid (negative or enormous), the function writes a
// message to stderr and returns 1'b0.
svBit OtbnMemUtilGetSegData(OtbnMemUtil *mem_util, svBit is_imem, int word_off,
                            /* output bit[31:0] */ svBitVecVal *data_value);
}
