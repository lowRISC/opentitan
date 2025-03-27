// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_IMM_SECTION_IMM_SECTION_VERSION_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_IMM_SECTION_IMM_SECTION_VERSION_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"

#ifdef __cplusplus
extern "C" {
#endif

/*
 * The version struct is stored at the last 16 bytes of imm_section.
 */
enum {
  kImmVersionSize = 16,
};

/**
 * Version info append at the end of built imm_section.
 */
typedef struct imm_section_version {
  /**
   * Major version (breaking changes).
   *
   * The version is defined in the bazel file:
   *   sw/device/silicon_creator/rom_ext/imm_section/defs.bzl
   */
  uint8_t major;
  /**
   * Minor version (non-breaking changes).
   *
   * The version is defined in the bazel file:
   *   sw/device/silicon_creator/rom_ext/imm_section/defs.bzl
   */
  uint8_t minor;
  /**
   * Reserved space for future update.
   */
  uint8_t reserved[14];
} imm_section_version_t;

OT_ASSERT_MEMBER_OFFSET(imm_section_version_t, major, 0);
OT_ASSERT_MEMBER_OFFSET(imm_section_version_t, minor, 1);
OT_ASSERT_SIZE(imm_section_version_t, 16);

#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_IMM_SECTION_IMM_SECTION_VERSION_H_
