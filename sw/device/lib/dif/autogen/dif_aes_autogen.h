// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_AES_AUTOGEN_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_AES_AUTOGEN_H_

// THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:
// util/make_new_dif.py --mode=regen --only=autogen

/**
 * @file
 * @brief <a href="/hw/ip/aes/doc/">AES</a> Device Interface Functions
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
 * A handle to aes.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_aes {
  /**
   * The base address for the aes hardware registers.
   */
  mmio_region_t base_addr;
} dif_aes_t;

/**
 * Creates a new handle for a(n) aes peripheral.
 *
 * This function does not actuate the hardware.
 *
 * @param base_addr The MMIO base address of the aes peripheral.
 * @param[out] aes Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aes_init(mmio_region_t base_addr, dif_aes_t *aes);

/**
 * A aes alert type.
 */
typedef enum dif_aes_alert {
  /**
   * This recoverable alert is triggered upon detecting an update error in the
   * shadowed Control Register. The content of the Control Register is not
   * modified (See Control Register). The AES unit can be recovered from such a
   * condition by restarting the AES operation, i.e., by re-writing the Control
   * Register. This should be monitored by the system.
   */
  kDifAesAlertRecovCtrlUpdateErr = 0,
  /**
   * This fatal alert is triggered upon detecting a fatal fault inside the AES
   * unit. Examples for such faults include i) storage errors in the shadowed
   * Control Register, ii) any internal FSM entering an invalid state, iii) any
   * sparsely encoded signal taking on an invalid value, iv) errors in the
   * internal round counter, v) escalations triggered by the life cycle
   * controller, and vi) fatal integrity failures on the TL-UL bus. The AES unit
   * cannot recover from such an error and needs to be reset.
   */
  kDifAesAlertFatalFault = 1,
} dif_aes_alert_t;

/**
 * Forces a particular alert, causing it to be escalated as if the hardware
 * had raised it.
 *
 * @param aes A aes handle.
 * @param alert The alert to force.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_aes_alert_force(const dif_aes_t *aes, dif_aes_alert_t alert);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_AUTOGEN_DIF_AES_AUTOGEN_H_
