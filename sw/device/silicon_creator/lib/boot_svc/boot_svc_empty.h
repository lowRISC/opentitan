// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_EMPTY_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_EMPTY_H_

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_header.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

enum {
  kBootSvcEmptyType = 0xb4594546,
  kBootSvcEmptyPayloadWordCount =
      CHIP_BOOT_SVC_MSG_PAYLOAD_SIZE_MAX / sizeof(uint32_t),
};

/**
 * An empty boot services message.
 *
 * This message type consists of a payload that is as large as the largest boot
 * services message. ROM_EXT should use an object of this type to initialize the
 * boot services area in the retention SRAM or to clear a boot services request
 * before writing the response. Silicon owner code should use an object of this
 * type to clear a boot services response.
 */

typedef struct boot_svc_empty {
  /**
   * Boot services message header.
   */
  boot_svc_header_t header;
  /**
   * An arbitrary payload.
   */
  uint32_t payload[kBootSvcEmptyPayloadWordCount];
} boot_svc_empty_t;

OT_ASSERT_MEMBER_OFFSET(boot_svc_empty_t, header, 0);
OT_ASSERT_MEMBER_OFFSET(boot_svc_empty_t, payload,
                        CHIP_BOOT_SVC_MSG_HEADER_SIZE);
OT_ASSERT_SIZE(boot_svc_empty_t, CHIP_BOOT_SVC_MSG_SIZE_MAX);

/**
 * Initialize an empty boot services message.
 *
 * @param[out] msg Output buffer for the message.
 */
void boot_svc_empty_init(boot_svc_empty_t *msg);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_EMPTY_H_
