// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_HEADER_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_HEADER_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Boot services message header.
 *
 * All boot services messages start with a common header followed by a message
 * specific payload.
 */
typedef struct boot_svc_header {
  /**
   * SHA256 digest of the message.
   *
   * Digest region starts at `identifier` and extends until the end of the
   * message.
   */
  hmac_digest_t digest;
  /**
   * Identifier.
   *
   * This field must be `kBootSvcIdentifier` for boot service messages that use
   * this header format.
   */
  uint32_t identifier;
  /**
   * Type of the message.
   */
  uint32_t type;
  /**
   * Total length of the message in bytes.
   */
  uint32_t length;
} boot_svc_header_t;

OT_ASSERT_MEMBER_OFFSET(boot_svc_header_t, digest, 0);
OT_ASSERT_MEMBER_OFFSET(boot_svc_header_t, identifier, 32);
OT_ASSERT_MEMBER_OFFSET(boot_svc_header_t, type, 36);
OT_ASSERT_MEMBER_OFFSET(boot_svc_header_t, length, 40);
OT_ASSERT_SIZE(boot_svc_header_t, CHIP_BOOT_SVC_MSG_HEADER_SIZE);

enum {
  /**
   * Common identifier shared by all boot services messages.
   *
   * ASCII "BSVC".
   */
  kBootSvcIdentifier = 0x43565342,
};

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_HEADER_H_
