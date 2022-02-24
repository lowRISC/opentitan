// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_RSTMGR_AUTOGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_RSTMGR_AUTOGEN_H_

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

/**
 * @file
 * @brief <a href="/hw/ip/rstmgr/doc/">RSTMGR</a> Device Interface Functions
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
 * A handle to rstmgr.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_rstmgr {
  /**
   * The base address for the rstmgr hardware registers.
   */
  mmio_region_t base_addr;
} dif_rstmgr_t;

/**
 * Creates a new handle for a(n) rstmgr peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param base_addr The MMIO base address of the rstmgr peripheral.
 * @param[out] rstmgr Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rstmgr_init(mmio_region_t base_addr, dif_rstmgr_t *rstmgr);

/**
 * A rstmgr alert type.
 */
typedef enum dif_rstmgr_alert {
  /**
   * This fatal alert is triggered when a fatal structural fault is detected.
   * Structural faults include errors such as sparse fsm errors and tlul
   * integrity errors.
   */
  kDifRstmgrAlertFatalFault = 0,
  /**
   * This fatal alert is triggered when a reset consistency fault is detected.
   * It is separated from the category above for clearer error collection and
   * debug.
   */
  kDifRstmgrAlertFatalCnstyFault = 1,
} dif_rstmgr_alert_t;

/**
 * Forces a particular alert, causing it to be escalated as if the hardware
 * had raised it.
 *
 * @param rstmgr A rstmgr handle.
 * @param alert The alert to force.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rstmgr_alert_force(const dif_rstmgr_t *rstmgr,
                                    dif_rstmgr_alert_t alert);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_RSTMGR_AUTOGEN_H_
