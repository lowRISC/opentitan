// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_RV_CORE_IBEX_AUTOGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_RV_CORE_IBEX_AUTOGEN_H_

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

/**
 * @file
 * @brief <a href="/hw/ip/rv_core_ibex/doc/">RV_CORE_IBEX</a> Device Interface
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
 * A handle to rv_core_ibex.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_rv_core_ibex {
  /**
   * The base address for the rv_core_ibex hardware registers.
   */
  mmio_region_t base_addr;
} dif_rv_core_ibex_t;

/**
 * Creates a new handle for a(n) rv_core_ibex peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param base_addr The MMIO base address of the rv_core_ibex peripheral.
 * @param[out] rv_core_ibex Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_core_ibex_init(mmio_region_t base_addr,
                                   dif_rv_core_ibex_t *rv_core_ibex);

/**
 * A rv_core_ibex alert type.
 */
typedef enum dif_rv_core_ibex_alert {
  /**
   * Software triggered alert for fatal faults
   */
  kDifRvCoreIbexAlertFatalSwErr = 0,
  /**
   * Software triggered Alert for recoverable faults
   */
  kDifRvCoreIbexAlertRecovSwErr = 1,
  /**
   * Triggered when - Ibex raises `alert_major_internal_o` - Ibex raises
   * `alert_major_bus_o` - A double fault is seen (Ibex raises
   * `double_fault_seen_o`) - A bus integrity error is seen
   */
  kDifRvCoreIbexAlertFatalHwErr = 2,
  /**
   * Triggered when Ibex raises `alert_minor_o`
   */
  kDifRvCoreIbexAlertRecovHwErr = 3,
} dif_rv_core_ibex_alert_t;

/**
 * Forces a particular alert, causing it to be escalated as if the hardware
 * had raised it.
 *
 * @param rv_core_ibex A rv_core_ibex handle.
 * @param alert The alert to force.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rv_core_ibex_alert_force(
    const dif_rv_core_ibex_t *rv_core_ibex, dif_rv_core_ibex_alert_t alert);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_RV_CORE_IBEX_AUTOGEN_H_
