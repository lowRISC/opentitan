// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CHIP_INFO_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CHIP_INFO_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"

/**
 * A truncated commit hash from the open-source OpenTitan repo that can be
 * used to reproduce the ROM binary.
 */
typedef struct chip_info_scm_revision {
  /**
   * Least significant word of the truncated commit hash.
   */
  uint32_t scm_revision_low;
  /**
   * Most significant word of the truncated commit hash.
   */
  uint32_t scm_revision_high;
} chip_info_scm_revision_t;

typedef struct chip_info {
  /**
   * Truncated commit hash.
   */
  chip_info_scm_revision_t scm_revision;
  /**
   * Chip info format version.
   *
   * The chip info struct is placed at the end of the ROM. Placing this field at
   * the end of the struct places the version word at the last addressable ROM
   * address, which gives later boot stages a fixed address to look for this
   * field. See `sw/device/silicon_creator/rom/rom.ld` for details.
   */
  uint32_t version;
} chip_info_t;
OT_ASSERT_MEMBER_OFFSET(chip_info_t, scm_revision, 0);
OT_ASSERT_MEMBER_OFFSET(chip_info_t, version, 8);
OT_ASSERT_SIZE(chip_info_t, 12);

enum {
  /**
   * Chip info format version 1 value.
   */
  kChipInfoVersion1 = 0x4efecea6,
};

/**
 * Extern declaration for the `kChipInfo` instance placed at the end of ROM.
 *
 * The actual definition is in an auto-generated file.
 */
extern const chip_info_t kChipInfo;

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CHIP_INFO_H_
