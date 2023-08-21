// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_LOG_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_LOG_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/chip_info.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

typedef struct boot_log {
  hmac_digest_t digest;
  uint32_t identifier;
  chip_info_scm_revision_t chip_version;
  uint32_t rom_ext_slot;
  uint32_t bl0_slot;
} boot_log_t;

OT_ASSERT_MEMBER_OFFSET(boot_log_t, digest, 0);
OT_ASSERT_MEMBER_OFFSET(boot_log_t, identifier, 32);
OT_ASSERT_MEMBER_OFFSET(boot_log_t, chip_version, 36);
OT_ASSERT_MEMBER_OFFSET(boot_log_t, rom_ext_slot, 44);
OT_ASSERT_MEMBER_OFFSET(boot_log_t, bl0_slot, 48);

enum {
  /**
   * Boot log identifier value (ASCII "BOLG").
   */
  kBootLogIdentifier = 0x474c4f42,

  /**
   * Boot Slot designators
   *
   * Encoding generated with:
   * $ ./util/design/sparse-fsm-encode.py -d 6 -m 5 -n 32 \
   *     -s 2335952935 --language=c
   *
   * Minimum Hamming distance: 12
   * Maximum Hamming distance: 21
   * Minimum Hamming weight: 18
   * Maximum Hamming weight: 22
   */
  kRomExtBootSlotA = 0x5abf68ea,
  kRomExtBootSlotB = 0x53ebdf83,
  kBl0BootSlotA = 0xb851f57e,
  kBl0BootSlotB = 0x17cfb6bf,

  /**
   * Indicates an unpopulated field in the boot log.
   */
  kBootLogUninitialized = 0xe67f0d52,
};

/**
 * Updates the digest of the boot_log.
 *
 * This function computes the digest over all fields of the boot_log_t struct
 * (except digest) and updates the digest field. The digest must be the first
 * member of the struct.
 *
 * @param boot_log A buffer that holds the boot_log.
 */
void boot_log_digest_update(boot_log_t *boot_log);

/**
 * Checks whether a boot_log entry is valid.
 *
 * This function checks the `identifier` and `digest` fields of the given
 * `boot_log`.
 *
 * @param boot_log A buffer that holds the boot_log.
 * @return Whether the digest and identifier of the `boot_log` are valid.
 */
OT_WARN_UNUSED_RESULT
rom_error_t boot_log_check(const boot_log_t *boot_log);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_LOG_H_
