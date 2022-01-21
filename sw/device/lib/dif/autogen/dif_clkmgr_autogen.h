// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_CLKMGR_AUTOGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_CLKMGR_AUTOGEN_H_

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

/**
 * @file
 * @brief <a href="/hw/ip/clkmgr/doc/">CLKMGR</a> Device Interface Functions
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
 * A handle to clkmgr.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_clkmgr {
  /**
   * The base address for the clkmgr hardware registers.
   */
  mmio_region_t base_addr;
} dif_clkmgr_t;

/**
 * Creates a new handle for a(n) clkmgr peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param base_addr The MMIO base address of the clkmgr peripheral.
 * @param[out] clkmgr Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_clkmgr_init(mmio_region_t base_addr, dif_clkmgr_t *clkmgr);

/**
 * A clkmgr alert type.
 */
typedef enum dif_clkmgr_alert {
  /**
   * This recoverable alert is triggered when there are measurement errors.
   */
  kDifClkmgrAlertRecovFault = 0,
  /**
   * This fatal alert is triggered when a fatal TL-UL bus integrity fault is
   * detected.
   */
  kDifClkmgrAlertFatalFault = 1,
} dif_clkmgr_alert_t;

/**
 * Forces a particular alert, causing it to be escalated as if the hardware
 * had raised it.
 *
 * @param clkmgr A clkmgr handle.
 * @param alert The alert to force.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_clkmgr_alert_force(const dif_clkmgr_t *clkmgr,
                                    dif_clkmgr_alert_t alert);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_CLKMGR_AUTOGEN_H_
