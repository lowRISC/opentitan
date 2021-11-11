// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_SRAM_CTRL_AUTOGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_SRAM_CTRL_AUTOGEN_H_

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

/**
 * @file
 * @brief <a href="/hw/ip/sram_ctrl/doc/">SRAM_CTRL</a> Device Interface
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
 * A handle to sram_ctrl.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_sram_ctrl {
  /**
   * The base address for the sram_ctrl hardware registers.
   */
  mmio_region_t base_addr;
} dif_sram_ctrl_t;

/**
 * Creates a new handle for a(n) sram_ctrl peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param base_addr The MMIO base address of the sram_ctrl peripheral.
 * @param[out] sram_ctrl Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sram_ctrl_init(mmio_region_t base_addr,
                                dif_sram_ctrl_t *sram_ctrl);

/**
 * A sram_ctrl alert type.
 */
typedef enum dif_sram_ctrl_alert {
  /**
   * This fatal alert is triggered when a fatal TL-UL bus integrity fault is
   * detected, or if the initialization mechanism has reached an invalid state.
   */
  kDifSramCtrlAlertFatalError = 0,
} dif_sram_ctrl_alert_t;

/**
 * Forces a particular alert, causing it to be escalated as if the hardware
 * had raised it.
 *
 * @param sram_ctrl A sram_ctrl handle.
 * @param alert The alert to force.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_sram_ctrl_alert_force(const dif_sram_ctrl_t *sram_ctrl,
                                       dif_sram_ctrl_alert_t alert);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_SRAM_CTRL_AUTOGEN_H_
