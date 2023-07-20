// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_CLKMGR_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_CLKMGR_H_

/**
 * @file
 * @brief <a href="/hw/ip/clkmgr/doc/">Clock Manager</a> Device Interface
 * Functions
 */

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "sw/device/lib/dif/autogen/dif_clkmgr_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * An Index of a "Gateable" Clock.
 *
 * "Gateable" clocks are under full software control: they can be enabled and
 * disabled by software, which directly starts and stops the identified clock.
 */
typedef uint32_t dif_clkmgr_gateable_clock_t;

/**
 * An Index of a "Hintable" Clock.
 *
 * "Hintable" clocks are under partial software control: software can suggest
 * they are stopped, but the clock manager may delay stopping the peripheral, or
 * may ignore the request altogether.
 */
typedef uint32_t dif_clkmgr_hintable_clock_t;

typedef enum dif_clkmgr_measure_clock {
  /**
   * The Io clock.
   */
  kDifClkmgrMeasureClockIo,
  /**
   * The Io_div2 clock.
   */
  kDifClkmgrMeasureClockIoDiv2,
  /**
   * The Io div4 clock.
   */
  kDifClkmgrMeasureClockIoDiv4,
  /**
   * The Main clock.
   */
  kDifClkmgrMeasureClockMain,
  /**
   * The Usb clock.
   */
  kDifClkmgrMeasureClockUsb,
} dif_clkmgr_measure_clock_t;

typedef enum dif_clkmgr_recov_err_type {
  /**
   * A recoverable update error for one of the clocks.
   */
  kDifClkmgrRecovErrTypeShadowUpdate = 1u << 0,
  /**
   * A recoverable measurement error for IO clock.
   */
  kDifClkmgrRecovErrTypeIoMeas = 1u << 1,
  /**
   * A recoverable measurement error for IO_DIV2 clock.
   */
  kDifClkmgrRecovErrTypeIoDiv2Meas = 1u << 2,
  /**
   * A recoverable measurement error for IO_DIV4 clock.
   */
  kDifClkmgrRecovErrTypeIoDiv4Meas = 1u << 3,
  /**
   * A recoverable measurement error for MAIN clock.
   */
  kDifClkmgrRecovErrTypeMainMeas = 1u << 4,
  /**
   * A recoverable measurement error for USB clock.
   */
  kDifClkmgrRecovErrTypeUsbMeas = 1u << 5,
  /**
   * A recoverable timeout error for IO clock.
   */
  kDifClkmgrRecovErrTypeIoTimeout = 1u << 6,
  /**
   * A recoverable timeout error for IO_DIV2 clock.
   */
  kDifClkmgrRecovErrTypeIoDiv2Timeout = 1u << 7,
  /**
   * A recoverable timeout error for IO_DIV4 clock.
   */
  kDifClkmgrRecovErrTypeIoDiv4Timeout = 1u << 8,
  /**
   * A recoverable timeout error for MAIN clock.
   */
  kDifClkmgrRecovErrTypeMainTimeout = 1u << 9,
  /**
   * A recoverable timeout error for USB clock.
   */
  kDifClkmgrRecovErrTypeUsbTimeout = 1u << 10,
} dif_clkmgr_recov_err_type_t;

/**
 * A set of recoverable errors.
 *
 * This type is used to clear and read the recoverable error codes.
 */
typedef uint32_t dif_clkmgr_recov_err_codes_t;

typedef enum dif_clkmgr_fatal_err_type {
  /**
   * A fatal error for regfile integrity.
   */
  kDifClkmgrFatalErrTypeRegfileIntegrity = 1u << 0,
  /**
   * A fatal error for a duplicate idle counter.
   */
  kDifClkmgrFatalErrTypeIdleCount = 1u << 1,
  /**
   * A fatal error for a shadow register storage.
   */
  kDifClkmgrFatalErrTypeShadowStorage = 1u << 2,
} dif_clkmgr_fatal_err_type_t;

/**
 * A set of fatal errors.
 *
 * This type is used to read the fatal error codes.
 */
typedef uint32_t dif_clkmgr_fatal_err_codes_t;

/**
 * Check if jitter is Enabled.
 * @param clkmgr Clock Manager Handle.
 * @param[out] is_enabled whether jitter is enabled or not.
 * @returns The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_clkmgr_jitter_get_enabled(const dif_clkmgr_t *clkmgr,
                                           dif_toggle_t *state);

/**
 * Enable of Disable jitter.
 * @param clkmgr Clock Manager Handle.
 * @param new_state whether to enable or disable jitter.
 * @returns The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_clkmgr_jitter_set_enabled(const dif_clkmgr_t *clkmgr,
                                           dif_toggle_t new_state);

/**
 * Check if a Gateable Clock is Enabled or Disabled.
 *
 * @param clkmgr Clock Manager Handle.
 * @param clock Gateable Clock ID.
 * @param[out] is_enabled whether the clock is enabled or not.
 * @returns The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_clkmgr_gateable_clock_get_enabled(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_gateable_clock_t clock,
    dif_toggle_t *state);

/**
 * Enable or Disable a Gateable Clock.
 *
 * @param clkmgr Clock Manager Handle.
 * @param clock Gateable Clock ID.
 * @param new_state whether to enable or disable the clock.
 * @returns The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_clkmgr_gateable_clock_set_enabled(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_gateable_clock_t clock,
    dif_toggle_t new_state);

/**
 * Check if a Hintable Clock is Enabled or Disabled.
 *
 * Hintable clocks are not under full software control, but this operation
 * accurately reflects the state of the current clock, regardless of any hint
 * requests made by software.
 *
 * To read what hint the software has given the hardware, use
 * #dif_clkmgr_hintable_clock_get_hint.
 *
 * @param clkmgr Clock Manager Handle.
 * @param clock Hintable Clock ID.
 * @param[out] is_enabled whether the clock is enabled or not.
 * @returns The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_clkmgr_hintable_clock_get_enabled(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_hintable_clock_t clock,
    dif_toggle_t *state);

/**
 * Enable or Disable a Hintable Clock.
 *
 * This only sets a hint that the clock should be enabled or disabled. The clock
 * manager is in control of whether the clock should actually be enabled or
 * disabled.
 *
 * To read what hint the software has given the hardware, use
 * #dif_clkmgr_hintable_clock_get_hint. To read whether the clock is currently
 * enabled or disabled, use #dif_clkmgr_hintable_clock_get_enabled.
 *
 * @param clkmgr Clock Manager Handle.
 * @param clock Hintable Clock ID.
 * @param new_state whether to enable or disable the clock.
 * @returns The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_clkmgr_hintable_clock_set_hint(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_hintable_clock_t clock,
    dif_toggle_t new_state);

/**
 * Read the current Hint for a Hintable Clock.
 *
 * Hintable clocks are not under full software control; this operation
 * accurately reflects the current software hint, not the current state of the
 * clock.
 *
 * To read whether the clock is currently enabled or disabled, use
 * #dif_clkmgr_hintable_clock_get_enabled.
 *
 * @param clkmgr Clock Manager Handle.
 * @param clock Hintable Clock ID.
 * @param[out] hinted_is_enabled the current software request (hint) for this
 * clock.
 * @returns The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_clkmgr_hintable_clock_get_hint(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_hintable_clock_t clock,
    dif_toggle_t *state);

/**
 * Enable chip to use the external clock.
 *
 * @param clkmgr Clock Manager Handle.
 * @param is_low_speed External clock is low speed or high speed.
 * @returns The result of the operation.
 * High speed - external clock is close to nominal speeds (e.g. external clock
 * is 96MHz and nominal frequency is 96MHz-100MHz). Low speed - external clock
 * is half of nominal speeds (e.g. external clock is 48MHz and nominal frequency
 * is 96MHz-100MHz).
 *
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_clkmgr_external_clock_set_enabled(const dif_clkmgr_t *clkmgr,
                                                   bool is_low_speed);

/**
 * Disable chip to use the external clock.
 *
 * @param clkmgr Clock Manager Handle.
 * @returns The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_clkmgr_external_clock_set_disabled(const dif_clkmgr_t *clkmgr);

/**
 * Determine if the transition to using external clock is complete.
 *
 * @param clkmgr Clock Manager Handle.
 * @param[out] status Set to true if the transition is complete.
 * @returns The result of the operation once it completes.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_clkmgr_external_clock_is_settled(const dif_clkmgr_t *clkmgr,
                                                  bool *status);

/**
 * Disable measurement control updates.
 *
 * This can only be disabled, and stays disabled until the next POR.
 *
 * @param clkmgr Clock Manager Handle.
 * @returns The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_clkmgr_measure_ctrl_disable(const dif_clkmgr_t *clkmgr);

/**
 * Get measurement control state.
 *
 * @param clkmgr Clock Manager Handle.
 * @param[out] state The state of control enable.
 * @returns The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_clkmgr_measure_ctrl_get_enable(const dif_clkmgr_t *clkmgr,
                                                dif_toggle_t *state);

/**
 * Configure count measurements.
 *
 * @param clkmgr Clock Manager Handle.
 * @param clock A clock to be measured.
 * @param min_threshold The smallest permissible cycle count.
 * @param max_threshold The largest permissible cycle count.
 * @returns The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_clkmgr_enable_measure_counts(const dif_clkmgr_t *clkmgr,
                                              dif_clkmgr_measure_clock_t clock,
                                              uint32_t min_threshold,
                                              uint32_t max_threshold);

/**
 * Disable count measurements.
 *
 * Does not modify the thresholds.
 *
 * @param clkmgr Clock Manager Handle.
 * @param clock A clock to be measured.
 * @returns The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_clkmgr_disable_measure_counts(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_measure_clock_t clock);

/**
 * Get the count measurement enable.
 *
 * @param clkmgr Clock Manager Handle.
 * @param clock A clock to be measured.
 * @param[out] state The state of control enable.
 * @returns The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_clkmgr_measure_counts_get_enable(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_measure_clock_t clock,
    dif_toggle_t *state);

/**
 * Get the count measurement thresholds.
 *
 * @param clkmgr Clock Manager Handle.
 * @param clock A clock to be measured.
 * @param[out] min_threshold The minumum threshold.
 * @param[out] max_threshold The maximum threshold.
 * @returns The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_clkmgr_measure_counts_get_thresholds(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_measure_clock_t clock,
    uint32_t *min_threshold, uint32_t *max_threshold);

/**
 * Read the recoverable error codes.
 *
 * @param clkmgr Clock Manager Handle.
 * @param[out] codes The recoverable error codes.
 * @returns The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_clkmgr_recov_err_code_get_codes(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_recov_err_codes_t *codes);

/**
 * Clear selected recoverable error codes.
 *
 * @param clkmgr Clock Manager Handle.
 * @param codes The recoverable error codes to be cleared.
 * @returns The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_clkmgr_recov_err_code_clear_codes(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_recov_err_codes_t codes);

/**
 * Read the fatal error codes.
 *
 * @param clkmgr Clock Manager Handle.
 * @param[out] codes The fatal error codes.
 * @returns The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_clkmgr_fatal_err_code_get_codes(
    const dif_clkmgr_t *clkmgr, dif_clkmgr_fatal_err_codes_t *codes);

/**
 * Wait for external clock switch to finish.
 *
 * @param clkmgr Clock Manager Handle.
 * @returns The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_clkmgr_wait_for_ext_clk_switch(const dif_clkmgr_t *clkmgr);
#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_CLKMGR_H_
