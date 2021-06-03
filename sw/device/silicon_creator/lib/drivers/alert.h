// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_ALERT_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_ALERT_H_
#include <stddef.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

#define ALERT_CLASSES 4

// Note: the AlertClass values need to map to a byte.
/**
 * Alert Classification Values as stored in OTP.
 */
typedef enum AlertClass {
  /***
   * Alert class X is a special class which means "not configured"
   */
  kAlertClassX,
  kAlertClassA,
  kAlertClassB,
  kAlertClassC,
  kAlertClassD,
} alert_class_t;

// Note: the AlertEnable values need to map to a byte.
/**
 * Alert Enable Values as stored in OTP.
 */
typedef enum AlertEnable {
  kAlertEnableNone,
  kAlertEnableEnabled,
  kAlertEnableLocked,
} alert_enable_t;

/**
 * Alert Escalation Policy as stored in OTP.  Note that each phase implies the
 * prior phases are also enabled.
 */
typedef enum AlertEscalate {
  kAlertEscalateNone,
  kAlertEscalatePhase0,
  kAlertEscalatePhase1,
  kAlertEscalatePhase2,
  kAlertEscalatePhase3,
} alert_escalate_t;

/**
 * Alert class configuration struct.
 */
typedef struct AlertClassConfig {
  /**
   * Whether or not this alert class enabled.
   */
  alert_enable_t enabled;
  /**
   * The escalation configuration for this alert class.
   */
  alert_escalate_t escalation;
  /**
   * The accumlation threshold for this alert class.
   */
  uint32_t accum_threshold;
  /**
   * The timeout cycles for this alert class.
   */
  uint32_t timeout_cycles;
  /**
   * The phase cycles for this alert class.
   */
  uint32_t phase_cycles[4];
} alert_class_config_t;

/**
 * Configure a single alert.
 *
 * Configures and optionally lock an alert's class configuration.
 *
 * @param index: The alert number.
 * @param cls: Class of the alert.
 * @param enabled: Whether or not to enable and/or lock the alert.
 */
rom_error_t alert_configure(size_t index, alert_class_t cls,
                            alert_enable_t enabled);

/**
 * Configure a single local alert.
 *
 * Configures and optionally lock a local alert's class configuration.
 *
 * @param index: The local alert number.
 * @param cls: Class of the alert.
 * @param enabled: Whether or not to enable and/or lock the alert.
 */
rom_error_t alert_local_configure(size_t index, alert_class_t cls,
                                  alert_enable_t enabled);
/**
 * Configure an alert class.
 *
 * Configures an alert class to the specified config.
 *
 * @param cls: Class of the alert (alert class X is not permitted here).
 * @param config: The alert class' configuration.
 */
rom_error_t alert_class_configure(alert_class_t cls,
                                  const alert_class_config_t *config);

/**
 * Enable the ping timer mechanism.
 */
rom_error_t alert_ping_enable(void);

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_ALERT_H_
