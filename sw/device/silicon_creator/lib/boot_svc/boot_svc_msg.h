// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_MSG_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_MSG_H_

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_empty.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_header.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_min_bl0_sec_ver.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_next_boot_bl0_slot.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_primary_bl0_slot.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Table of boot services request and response types.
 *
 * Columns: Data type, `boot_svc_msg_t` union field name.
 * We use an X macro to generate the assertion that checks
 * the value of `CHIP_BOOT_SVC_MSG_SIZE_MAX`.
 */
// clang-format off
#define BOOT_SVC_MSGS_DEFINE(X) \
  /**
   * Next Boot BL0 Slot request and response.
   */ \
  X(boot_svc_next_boot_bl0_slot_req_t, next_boot_bl0_slot_req) \
  X(boot_svc_next_boot_bl0_slot_res_t, next_boot_bl0_slot_res) \
  /**
   * Set Minimum Security Version request and response.
   */ \
  X(boot_svc_min_bl0_sec_ver_req_t, min_bl0_sec_ver_req) \
  X(boot_svc_min_bl0_sec_ver_res_t, min_bl0_sec_ver_res) \
  /**
   * Set Primary BL0 Slot request and response.
   */ \
  X(boot_svc_primary_bl0_slot_req_t, primary_bl0_slot_req) \
  X(boot_svc_primary_bl0_slot_res_t, primary_bl0_slot_res)
// clang-format on

/**
 * Helper macro for declaring fields for boot services messages
 *
 * @param type_ Data type.
 * @param field_name_ `boot_svc_msg_t` union field name.
 */
#define BOOT_SVC_MSG_FIELD(type_, field_name_) type_ field_name_;

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
   * Boot services request and response messages.
   */
  BOOT_SVC_MSGS_DEFINE(BOOT_SVC_MSG_FIELD);
} boot_svc_msg_t;

/**
 * Helper macro for generating the equalities for checking that the value of
 * `CHIP_BOOT_SVC_MSG_SIZE_MAX` is equal to the size of at least one of the boot
 * services messages.
 *
 * Note that the macro expands to an incomplete expression that must be
 * terminated with `false`.
 *
 * @param type_ Data type.
 * @param field_name_ `boot_svc_msg_t` union field name.
 */
#define BOOT_SVC_SIZE_EQ_(type_, field_name_) \
  sizeof(type_) == CHIP_BOOT_SVC_MSG_SIZE_MAX ||

static_assert(BOOT_SVC_MSGS_DEFINE(BOOT_SVC_SIZE_EQ_) false,
              "CHIP_BOOT_SVC_MSG_SIZE_MAX must equal to the size of at least "
              "one of the boot services messages");

#undef BOOT_SVC_SIZE_EQ_

/**
 * Helper macro for generating the inequalities for checking that the value of
 * `CHIP_BOOT_SVC_MSG_SIZE_MAX` is greater than or equal to the sizes of all
 * boot services messages.
 *
 * Note that the macro expands to an incomplete expression that must be
 * terminated with `true`.
 *
 * @param type_ Data type.
 * @param field_name_ `boot_svc_msg_t` union field name.
 */
#define BOOT_SVC_SIZE_LE_(type_, field_name_) \
  sizeof(type_) <= CHIP_BOOT_SVC_MSG_SIZE_MAX &&

static_assert(BOOT_SVC_MSGS_DEFINE(BOOT_SVC_SIZE_LE_) true,
              "CHIP_BOOT_SVC_MSG_SIZE_MAX must be greater than or equal to the "
              "sizes of all of the boot services messages");

#undef BOOT_SVC_SIZE_LE_

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_BOOT_SVC_BOOT_SVC_MSG_H_
