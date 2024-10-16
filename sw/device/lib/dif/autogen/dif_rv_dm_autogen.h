// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_RV_DM_AUTOGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_RV_DM_AUTOGEN_H_

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

/**
 * @file
 * @brief <a href="/book/hw/ip/rv_dm/">RV_DM</a> Device Interface Functions
 */

#include <stdbool.h>
#include <stdint.h>

#include "dt_rv_dm.h"  // Generated.
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * A handle to rv_dm.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_rv_dm {
  /**
   * The base address for the rv_dm hardware registers.
   */
  mmio_region_t base_addr;
} dif_rv_dm_t;

/**
 * Creates a new handle for a(n) rv_dm peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param base_addr The MMIO base address of the rv_dm peripheral.
 * @param[out] rv_dm Out param for the initialized handle.
 * @return The result of the operation.
 *
 * DEPRECATED This function exists solely for the transition to
 * dt-based DIFs and will be removed in the future.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_dm_init(mmio_region_t base_addr, dif_rv_dm_t *rv_dm);

/**
 * Creates a new handle for a(n) rv_dm peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param dt The devicetable description of the device.
 * @param[out] rv_dm Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_dm_init_from_dt(const dt_rv_dm_t *dt, dif_rv_dm_t *rv_dm);

/**
 * A rv_dm alert type.
 */
typedef enum dif_rv_dm_alert {
  /**
   * This fatal alert is triggered when a fatal TL-UL bus integrity fault is
   * detected.
   */
  kDifRvDmAlertFatalFault = 0,
} dif_rv_dm_alert_t;

/**
 * Forces a particular alert, causing it to be escalated as if the hardware
 * had raised it.
 *
 * @param rv_dm A rv_dm handle.
 * @param alert The alert to force.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_dm_alert_force(const dif_rv_dm_t *rv_dm,
                                   dif_rv_dm_alert_t alert);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_RV_DM_AUTOGEN_H_
