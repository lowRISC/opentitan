// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_RSTMGR_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_RSTMGR_H_

#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <stdnoreturn.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Alert information or CPU crash dump captured by the reset manager during the
 * last reset.
 */
typedef struct rstmgr_info {
  /**
   * Length.
   */
  uint32_t length;
  /**
   * Alert information or CPU crash dump words.
   */
  uint32_t info[16];
} rstmgr_info_t;

/**
 * Reset reason bitfield indices.
 *
 * Note that the reset reasons are not necessarily mutually exclusive.
 */
typedef enum rstmgr_reason {
  /**
   * Power on reset (POR).
   */
  kRstmgrReasonPowerOn = 0,

  /**
   * Low power exit (LOW_POWER_EXIT).
   */
  kRstmgrReasonLowPowerExit = 1,

  /**
   * Software issued request (SW).
   */
  kRstmgrReasonSoftwareRequest = 2,

  /**
   * Hardware requests (HW_REQ).
   */
  kRstmgrReasonSysrstCtrl = 3,
  kRstmgrReasonWatchdog = 4,
  kRstmgrReasonPowerUnstable = 5,
  kRstmgrReasonEscalation = 6,
  /**
   * Non-debug module (NDM).
   */
  kRstmgrReasonNonDebugModule = 7,

  /**
   * Last used bit index (inclusive).
   */
  kRstmgrReasonLast = 7,
} rstmgr_reason_t;

/**
 * Get alert information captured during last reset.
 *
 * @param[out] info Alert information.
 */
void rstmgr_alert_info_collect(rstmgr_info_t *info);

/**
 * Get CPU crash dump captured during last reset.
 *
 * @param[out] info CPU crash dump.
 */
void rstmgr_cpu_info_collect(rstmgr_info_t *info);

/**
 * Get the reason(s) for the last reset.
 *
 * The reset reason is a bitfield. Individual bits may be extracted using
 * the indices provided by the `rstmgr_reason_t` enumeration. The reset
 * reasons are not necessarily mutually exclusive.
 */
OT_WARN_UNUSED_RESULT
uint32_t rstmgr_reason_get(void);

/**
 * Clear the reset reason(s) set in the given mask.
 *
 * A value of all ones will clear all the reset reasons while zero will
 * leave the register unchanged.
 *
 * @param reasons A mask containing the bit fields to clear.
 */
void rstmgr_reason_clear(uint32_t reasons);

/**
 * Enable capturing of alert info in the event of an alert escalation.
 */
void rstmgr_alert_info_enable(void);

/**
 * Enable capturing of CPU crash dump in the event of a crash.
 */
void rstmgr_cpu_info_enable(void);

/**
 * Requests a system reset.
 */
#ifdef OT_PLATFORM_RV32
// Omit `noreturn` to be able to test this function in off-target tests.
noreturn
#endif
    void
    rstmgr_reset(void);

/**
 * Verifies that info collection is initialized properly.
 *
 * In order not to interfere with the operation of other software on the chip,
 * this check is not enforced if `reasons` includes low power exit.
 *
 * @param reset_reasons Reset reasons.
 */
rom_error_t rstmgr_info_en_check(uint32_t reset_reasons);

/**
 * Bitfields for `OWNER_SW_CFG_ROM_RSTMGR_INFO_EN" OTP item.
 *
 * Defined here to be able to use in tests.
 */
#define RSTMGR_OTP_FIELD_ALERT_INFO_EN \
  (bitfield_field32_t) { .mask = UINT8_MAX, .index = CHAR_BIT * 0 }
#define RSTMGR_OTP_FIELD_CPU_INFO_EN \
  (bitfield_field32_t) { .mask = UINT8_MAX, .index = CHAR_BIT * 1 }

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_RSTMGR_H_
