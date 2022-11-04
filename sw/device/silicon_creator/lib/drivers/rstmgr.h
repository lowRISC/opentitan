// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_RSTMGR_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_RSTMGR_H_

#include <stddef.h>
#include <stdint.h>
#include <stdnoreturn.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Alert Infomation captured by the reset manager during the last reset.
 */
typedef struct RstMgrAlertInfo {
  /**
   * Length of alert information.
   */
  uint32_t length;
  /**
   * Alert info words.
   */
  uint32_t info[16];
} rstmgr_alert_info_t;

extern rstmgr_alert_info_t rstmgr_alert_info;

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
 * Get the reason(s) for the last reset.
 *
 * The reset reason is a bitfield. Individual bits may be extracted using
 * the indices provided by the `rstmgr_reason_t` enumeration. The reset
 * reasons are not necessarily mutually exclusive.
 *
 * This function also captures alert information into `rstmgr_alert_info`.
 */
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
 * Requests a system reset.
 */
#ifdef OT_PLATFORM_RV32
// Omit `noreturn` to be able to test this function in off-target tests.
noreturn
#endif
    void
    rstmgr_reset(void);

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_RSTMGR_H_
