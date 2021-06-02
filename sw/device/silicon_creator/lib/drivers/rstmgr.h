// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_RSTMGR_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_RSTMGR_H_

#include <stddef.h>
#include <stdint.h>

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
 * Get the reason for the last reset.
 *
 * This function also captures alert information into `rstmgr_alert_info`.
 */
uint32_t rstmgr_reason_get(void);

/**
 * Enable capturing of alert info in the event of an alert escalation.
 */
void rstmgr_alert_info_enable(void);

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_RSTMGR_H_
