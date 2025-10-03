// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BUILD_INFO_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BUILD_INFO_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"

/**
 * A truncated commit hash from the open-source OpenTitan repo that can be
 * used to reproduce the ROM binary.
 */
typedef struct build_info_scm_revision {
  /**
   * Least significant word of the truncated commit hash.
   */
  uint32_t scm_revision_low;
  /**
   * Most significant word of the truncated commit hash.
   */
  uint32_t scm_revision_high;
} build_info_scm_revision_t;

typedef struct build_info {
  /**
   * Truncated commit hash.
   */
  build_info_scm_revision_t scm_revision;
  /**
   * Chip info format version.
   *
   * The chip info struct is placed at the end of the ROM. Placing this field at
   * the end of the struct places the version word at the last addressable ROM
   * address, which gives later boot stages a fixed address to look for this
   * field. See `sw/device/silicon_creator/rom/rom.ld` for details.
   */
  uint32_t version;
} build_info_t;
OT_ASSERT_MEMBER_OFFSET(build_info_t, scm_revision, 0);
OT_ASSERT_MEMBER_OFFSET(build_info_t, version, 8);
OT_ASSERT_SIZE(build_info_t, 12);

enum {
  /**
   * Chip info format version 1 value.
   */
  kBuildInfoVersion1 = 0x4efecea6,
};

/**
 * The build information.
 */
extern const build_info_t kBuildInfo;

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BUILD_INFO_H_
