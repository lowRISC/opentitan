// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CHIP_INFO_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CHIP_INFO_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"

typedef struct chip_info {
  // A truncated commit hash from the open-source OpenTitan repo that can be
  // used to reproduce the ROM binary.
  uint64_t scm_revision;
} chip_info_t;

// This struct contains information about the ROM's provenance, and critically,
// it can be manually decoded from a hexdump. The linker script should place
// this at the top of the ROM.
extern const chip_info_t kChipInfo __attribute__((section(".chip_info")));

// Track the size of `kChipInfo` so we can compute how much space is left in the
// `.chip_info` section. If it becomes too large, linking will fail.
OT_ASSERT_SIZE(chip_info_t, 8);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CHIP_INFO_H_
