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
 * The version struct is stored at the last 32 bytes of imm_section.
 */
enum {
  kImmVersionSize = 32,
  kImmVersionMagic = 0x43534d49,
};

/**
 * Version info append at the end of built imm_section.
 */
typedef struct imm_section_version {
  /**
   * Magic Identifier 0x43534d49 `IMSC`.
   */
  uint32_t magic;
  /**
   * Major version (breaking changes).
   *
   * The version is defined in the bazel file:
   *   sw/device/silicon_creator/rom_ext/imm_section/defs.bzl
   */
  uint32_t major;
  /**
   * Minor version (non-breaking changes).
   *
   * The version is defined in the bazel file:
   *   sw/device/silicon_creator/rom_ext/imm_section/defs.bzl
   */
  uint32_t minor;
  /**
   * Build status modifiers.
   *
   * Values:
   *   ' '  : Git workspace is clean, or build without --stamp
   *   '+'  : Git workspace is dirty
   */
  char build_status;
  /**
   * Git commit hash truncated to first 4 bytes.
   *
   * This field will only be set when building with --stamp, zero otherwise.
   */
  uint32_t commit_hash;
  /**
   * Reserved space for future update.
   */
  uint8_t reserved[12];
} imm_section_version_t;

OT_ASSERT_MEMBER_OFFSET(imm_section_version_t, magic, 0);
OT_ASSERT_MEMBER_OFFSET(imm_section_version_t, major, 4);
OT_ASSERT_MEMBER_OFFSET(imm_section_version_t, minor, 8);
OT_ASSERT_MEMBER_OFFSET(imm_section_version_t, build_status, 12);
OT_ASSERT_MEMBER_OFFSET(imm_section_version_t, commit_hash, 16);
OT_ASSERT_SIZE(imm_section_version_t, 32);

#ifdef __cplusplus
}  // extern "C"
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_IMM_SECTION_IMM_SECTION_VERSION_H_
