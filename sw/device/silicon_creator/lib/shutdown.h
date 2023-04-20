// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SHUTDOWN_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_SHUTDOWN_H_
#include <stdint.h>
#include <stdnoreturn.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/error.h"
#ifdef __cplusplus
extern "C" {
#endif

/**
 * Evaluate an expression and call `shutdown_finalize` if the result is an
 * error.
 *
 * The error will be passed as an argument to `shutdown_finalize`.
 *
 * @param expr_ An expression which results in an rom_error_t.
 */
#define SHUTDOWN_IF_ERROR(expr_)         \
  do {                                   \
    rom_error_t error_ = expr_;          \
    if (launder32(error_) != kErrorOk) { \
      shutdown_finalize(error_);         \
    }                                    \
    HARDENED_CHECK_EQ(error_, kErrorOk); \
  } while (false)

/**
 * Initializes the ROM shutdown infrastructure.
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
 *
 * Encoding generated with
 * $ ./util/design/sparse-fsm-encode.py -d 5 -m 4 -n 32 \
 *     -s 208548646 --language=c
 *
 * Minimum Hamming distance: 14
 * Maximum Hamming distance: 18
 * Minimum Hamming weight: 13
 * Maximum Hamming weight: 18
 */
typedef enum shutdown_error_redact {
  kShutdownErrorRedactNone = 0xe2290aa5,
  kShutdownErrorRedactError = 0x3367d3d4,
  kShutdownErrorRedactModule = 0x1e791123,
  kShutdownErrorRedactAll = 0x48eb4bd9,
} shutdown_error_redact_t;

/**
 * Helper macro for encoding a 4 character prefix as a 32-bit value. The
 * resulting prefix is the concatenation of the given characters and ':'.
 */
#define LOG_PREFIX_(a_, b_, c_) (':' << 24 | (c_) << 16 | (b_) << 8 | (a_))

/**
 * Prefixes for error messages printed over UART.
 *
 * Note: Defined here for future use. These values are currently used only by
 * this module internally.
 *
 * See `ERROR_PREFIX_()`.
 */
typedef enum shutdown_log_prefix {
  kShutdownLogPrefixBootFault = LOG_PREFIX_('B', 'F', 'V'),
  kShutdownLogPrefixLifecycle = LOG_PREFIX_('L', 'C', 'V'),
  kShutdownLogPrefixVersion = LOG_PREFIX_('V', 'E', 'R'),
} shutdown_log_prefix_t;

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
 * Perform a shutdown in the ROM in response to an exceptional condition.
 *
 * @param reason A reason for entering the shutdown state.
 */
#ifdef OT_PLATFORM_RV32
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
