// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_ROM_CTRL_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_ROM_CTRL_H_

/**
 * @file
 * @brief <a href="/hw/ip/rom_ctrl/doc/">ROM Controller</a> Device Interface
 * Functions
 */

#include <stdint.h>

#include "rom_ctrl_regs.h"  // Generated.
#include "sw/device/lib/dif/autogen/dif_rom_ctrl_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * A fatal alert cause error.
 *
 * See also: `dif_rom_ctrl_fatal_alert_causes_t`.
 */
typedef enum dif_rom_ctrl_fatal_alert_cause {
  /**
   * No error has occured.
   */
  kDifRomCtrlFatalAlertCauseNoError = 0,
  /**
   * Set on a fatal error detected by the ROM checker.
   */
  kDifRomCtrlFatalAlertCauseCheckerError =
      ROM_CTRL_FATAL_ALERT_CAUSE_CHECKER_ERROR_BIT,
  /**
   * Set on an integrity error from the register interface.
   */
  kDifRomCtrlFatalAlertCauseIntegrityError =
      ROM_CTRL_FATAL_ALERT_CAUSE_INTEGRITY_ERROR_BIT,
} dif_rom_ctrl_fatal_alert_cause_t;

/**
 * A set of fatal alert cause errors.
 */
typedef uint32_t dif_rom_ctrl_fatal_alert_causes_t;

/**
 * A typed representation of the ROM digest.
 */
typedef struct dif_rom_ctrl_digest {
  uint32_t digest[ROM_CTRL_DIGEST_MULTIREG_COUNT];
} dif_rom_ctrl_digest_t;

/**
 * Reads the fatal alert cause bits of the ROM Controller.
 *
 * @param rom_ctrl A ROM Controller handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rom_ctrl_get_fatal_alert_cause(
    const dif_rom_ctrl_t *rom_ctrl,
    dif_rom_ctrl_fatal_alert_causes_t *alert_causes);

/**
 * Reads the (KMAC computed) ROM digest.
 *
 * @param rom_ctrl A ROM Controller handle.
 * @param digest KMAC digest of ROM.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rom_ctrl_get_digest(const dif_rom_ctrl_t *rom_ctrl,
                                     dif_rom_ctrl_digest_t *digest);

/**
 * Reads the expected ROM digest contained in the top eight words of ROM.
 *
 * @param rom_ctrl A ROM Controller handle.
 * @param expected_digest Expected KMAC digest of ROM.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_rom_ctrl_get_expected_digest(
    const dif_rom_ctrl_t *rom_ctrl, dif_rom_ctrl_digest_t *expected_digest);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_ROM_CTRL_H_
