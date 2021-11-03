// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_ROM_CTRL_AUTOGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_ROM_CTRL_AUTOGEN_H_

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

/**
 * @file
 * @brief <a href="/hw/ip/rom_ctrl/doc/">ROM_CTRL</a> Device Interface Functions
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
 * A handle to rom_ctrl.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_rom_ctrl {
  /**
   * The base address for the rom_ctrl hardware registers.
   */
  mmio_region_t base_addr;
} dif_rom_ctrl_t;

/**
 * Creates a new handle for a(n) rom_ctrl peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param base_addr The MMIO base address of the rom_ctrl peripheral.
 * @param[out] rom_ctrl Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rom_ctrl_init(mmio_region_t base_addr,
                               dif_rom_ctrl_t *rom_ctrl);

/**
 * A rom_ctrl alert type.
 */
typedef enum dif_rom_ctrl_alert {
  /**
   * A fatal error. Fatal alerts are non-recoverable and will be asserted until
   * a hard reset.
   */
  kDifRomCtrlAlertFatal = 0,
} dif_rom_ctrl_alert_t;

/**
 * Forces a particular alert, causing it to be escalated as if the hardware
 * had raised it.
 *
 * @param rom_ctrl A rom_ctrl handle.
 * @param alert The alert to force.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rom_ctrl_alert_force(const dif_rom_ctrl_t *rom_ctrl,
                                      dif_rom_ctrl_alert_t alert);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_ROM_CTRL_AUTOGEN_H_
