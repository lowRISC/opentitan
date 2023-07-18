// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_MSG_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_MSG_H_

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_empty.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_header.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_next_boot_bl0_slot.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * A Boot Services message.
 *
 * This is defined as a union where the common initial sequence is a
 * `boot_svc_header_t`. This makes it possible to store and read different types
 * of messages to the same location without invoking undefined behavior.
 */
typedef union boot_svc_msg {
  /**
   * Common initial sequence.
   */
  boot_svc_header_t header;
  /**
   * Empty boot services message.
   */
  boot_svc_empty_t empty;
  /**
   * Next Boot BL0 Slot request message.
   */
  boot_svc_next_boot_bl0_slot_req_t next_boot_bl0_slot_req;
  /**
   * Next Boot BL0 Slot response message.
   */
  boot_svc_next_boot_bl0_slot_res_t next_boot_bl0_slot_res;
} boot_svc_msg_t;
// TODO: Add an assertion for checking that CHIP_BOOT_SVC_MSG_SIZE_MAX is
// up to date after defining structs for other messages.
OT_ASSERT_SIZE(boot_svc_msg_t, CHIP_BOOT_SVC_MSG_SIZE_MAX);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_MSG_H_
