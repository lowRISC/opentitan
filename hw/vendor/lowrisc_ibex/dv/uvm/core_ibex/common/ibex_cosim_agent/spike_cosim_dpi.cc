// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <svdpi.h>
#include <cassert>

#include "cosim.h"
#include "spike_cosim.h"

extern "C" {
void *spike_cosim_init(const char *isa_string, svBitVecVal *start_pc,
                       svBitVecVal *start_mtvec,
                       const char *log_file_path_cstr) {
  assert(isa_string);

  std::string log_file_path;

  if (log_file_path_cstr) {
    log_file_path = log_file_path_cstr;
  }

  SpikeCosim *cosim = new SpikeCosim(isa_string, start_pc[0], start_mtvec[0],
                                     log_file_path, false, true);
  cosim->add_memory(0x80000000, 0x80000000);
  return static_cast<Cosim *>(cosim);
}

void spike_cosim_release(void *cosim_handle) {
  auto cosim = static_cast<Cosim *>(cosim_handle);

  delete cosim;
}
}
