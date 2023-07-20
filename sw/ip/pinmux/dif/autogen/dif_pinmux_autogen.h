// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_PINMUX_AUTOGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_PINMUX_AUTOGEN_H_

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

/**
 * @file
 * @brief <a href="/hw/ip/pinmux/doc/">PINMUX</a> Device Interface Functions
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
 * A handle to pinmux.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_pinmux {
  /**
   * The base address for the pinmux hardware registers.
   */
  mmio_region_t base_addr;
} dif_pinmux_t;

/**
 * Creates a new handle for a(n) pinmux peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param base_addr The MMIO base address of the pinmux peripheral.
 * @param[out] pinmux Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pinmux_init(mmio_region_t base_addr, dif_pinmux_t *pinmux);

/**
 * A pinmux alert type.
 */
typedef enum dif_pinmux_alert {
  /**
   * This fatal alert is triggered when a fatal TL-UL bus integrity fault is
   * detected.
   */
  kDifPinmuxAlertFatalFault = 0,
} dif_pinmux_alert_t;

/**
 * Forces a particular alert, causing it to be escalated as if the hardware
 * had raised it.
 *
 * @param pinmux A pinmux handle.
 * @param alert The alert to force.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pinmux_alert_force(const dif_pinmux_t *pinmux,
                                    dif_pinmux_alert_t alert);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_PINMUX_AUTOGEN_H_
