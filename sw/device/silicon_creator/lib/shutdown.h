// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SHUTDOWN_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SHUTDOWN_H_
#include <stdint.h>
#include <stdnoreturn.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#ifdef __cplusplus
extern "C" {
#endif

/**
 * Initializes the Mask ROM shutdown infrastructure.
 *
 * Reads the shutdown policy from OTP, and initializes the alert handler.
 *
 * @param lc_state: Lifecycle state of the chip.
 * @param[out] redaction Redaction level initialized according to the lifecycle
 * state and OTP configuration.
 * @return: Any error encountered during initialization.
 */
rom_error_t shutdown_init(lifecycle_state_t lc_state);

/**
 * The error redaction possibilities in increasing severity.
 *
 * This value is read from the ROM_ERROR_REPORTING OTP word.
 *
 * No error code redaction
 * Redact the specific error code.
 * Redact the specific error code and source modules.
 * Redact all error componens (general code, specific code and module).
 */
// TODO(lowRISC/opentitan#7148): Choose values for configuration enums.
typedef enum shutdown_error_redact {
  kShutdownErrorRedactNone,
  kShutdownErrorRedactError,
  kShutdownErrorRedactModule,
  kShutdownErrorRedactAll,
} shutdown_error_redact_t;

/**
 * Calculate the error redaction level required given the current lifecycle
 * state and OTP configuration.
 *
 * @return Redaction level to apply to error codes.
 */
OT_WARN_UNUSED_RESULT
shutdown_error_redact_t shutdown_redact_policy(void);

/**
 * Redact an error code.
 *
 * @param reason: The error code to be redacted.
 * @param severity: The redaction severity.
 * @return: The redacted error code.
 */
uint32_t shutdown_redact(rom_error_t reason, shutdown_error_redact_t severity);

/**
 * Perform a shutdown in the Mask ROM in response to an exceptional condition.
 *
 * @param reason A reason for entering the shutdown state.
 */
#ifndef OT_OFF_TARGET_TEST
// If this is a test, we'll omit `noreturn` so we can call this function
// from within a test program.
noreturn
#endif
    void
    shutdown_finalize(rom_error_t reason);

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SHUTDOWN_H_
