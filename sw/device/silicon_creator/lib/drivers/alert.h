// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_ALERT_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_ALERT_H_
#include <stddef.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

#define ALERT_CLASSES 4

/**
 * Alert Classification Values as stored in the ROM_ALERT_CLASSIFICATION and
 * ROM_LOCAL_ALERT_CLASSIFICATION fields in OTP.
 *
 * Encoding generated with
 * $ ./util/design/sparse-fsm-encode.py -d 2 -m 5 -n 8 \
 *     -s 3775359077 --language=c
 *
 * Minimum Hamming distance: 3
 * Maximum Hamming distance: 5
 * Minimum Hamming weight: 3
 * Maximum Hamming weight: 6
 */
typedef enum AlertClass {
  /***
   * Alert class X is a special class which means "not configured"
   */
  kAlertClassX = 0x94,
  kAlertClassA = 0xee,
  kAlertClassB = 0x64,
  kAlertClassC = 0xa7,
  kAlertClassD = 0x32,
} alert_class_t;

/**
 * Alert Enable Values as stored in the ROM_ALERT_CLASS_EN field in OTP.
 *
 * Encoding generated with
 * $ ./util/design/sparse-fsm-encode.py -d 5 -m 3 -n 8 \
 *     -s 999796195 --language=c
 *
 * Minimum Hamming distance: 5
 * Maximum Hamming distance: 6
 * Minimum Hamming weight: 3
 * Maximum Hamming weight: 4
 */
typedef enum AlertEnable {
  kAlertEnableNone = 0xa9,
  kAlertEnableEnabled = 0x07,
  kAlertEnableLocked = 0xd2,
} alert_enable_t;

/**
 * Alert Escalation Policy as stored in the ROM_ALERT_ESCALATION field in OTP.
 *
 * Note that each phase implies the prior phases are also enabled.
 *
 * Encoding generated with
 * $ ./util/design/sparse-fsm-encode.py -d 2 -m 5 -n 8 \
 *     -s 3525542881 --language=c
 *
 * Minimum Hamming distance: 3
 * Maximum Hamming distance: 6
 * Minimum Hamming weight: 3
 * Maximum Hamming weight: 5
 */
typedef enum AlertEscalate {
  kAlertEscalateNone = 0xd1,
  kAlertEscalatePhase0 = 0xb9,
  kAlertEscalatePhase1 = 0xcb,
  kAlertEscalatePhase2 = 0x25,
  kAlertEscalatePhase3 = 0x76,
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

/**
 * Compute the CRC32 of the configuration registers.
 *
 * @return CRC32 of the configuration registers.
 */
uint32_t alert_config_crc32(void);

/**
 * Compare the CRC32 of the configuration registers with the value in OTP.
 *
 * This function does not check the CRC32 in TEST_UNLOCKED* life cycle states to
 * allow a test program to configure the alert handler before transitioning to
 * other life cycle states.
 *
 * @param lc_state Life cycle state of the device.
 * @return result of the operation.
 */
rom_error_t alert_config_check(lifecycle_state_t lc_state);

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_ALERT_H_
