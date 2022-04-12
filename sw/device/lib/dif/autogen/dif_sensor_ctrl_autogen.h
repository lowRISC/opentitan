// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_SENSOR_CTRL_AUTOGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_SENSOR_CTRL_AUTOGEN_H_

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

/**
 * @file
 * @brief <a href="/hw/ip/sensor_ctrl/doc/">SENSOR_CTRL</a> Device Interface
 * Functions
 */

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * A handle to sensor_ctrl.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_sensor_ctrl {
  /**
   * The base address for the sensor_ctrl hardware registers.
   */
  mmio_region_t base_addr;
} dif_sensor_ctrl_t;

/**
 * Creates a new handle for a(n) sensor_ctrl peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param base_addr The MMIO base address of the sensor_ctrl peripheral.
 * @param[out] sensor_ctrl Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sensor_ctrl_init(mmio_region_t base_addr,
                                  dif_sensor_ctrl_t *sensor_ctrl);

/**
 * A sensor_ctrl alert type.
 */
typedef enum dif_sensor_ctrl_alert {
  /**
   * Recoverable sensor_ctrl alerts
   */
  kDifSensorCtrlAlertRecovAlert = 0,
  /**
   * Fatal sensor_ctrl alerts
   */
  kDifSensorCtrlAlertFatalAlert = 1,
} dif_sensor_ctrl_alert_t;

/**
 * Forces a particular alert, causing it to be escalated as if the hardware
 * had raised it.
 *
 * @param sensor_ctrl A sensor_ctrl handle.
 * @param alert The alert to force.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sensor_ctrl_alert_force(const dif_sensor_ctrl_t *sensor_ctrl,
                                         dif_sensor_ctrl_alert_t alert);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_SENSOR_CTRL_AUTOGEN_H_
