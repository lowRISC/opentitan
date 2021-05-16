// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_HW_IP_OTBN_DV_MODEL_SV_UTILS_H_
#define OPENTITAN_HW_IP_OTBN_DV_MODEL_SV_UTILS_H_

#include <svdpi.h>

// Utility function that packs a uint32_t into a SystemVerilog bit vector that
// represents a "bit [31:0]"
inline void set_sv_u32(svBitVecVal *dst, uint32_t src) {
  for (int i = 0; i < 32; ++i) {
    svBit bit = (src >> i) & 1;
    svPutBitselBit(dst, i, bit);
  }
}

#endif  // OPENTITAN_HW_IP_OTBN_DV_MODEL_SV_UTILS_H_
