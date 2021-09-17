// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SRAM_CTRL_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SRAM_CTRL_H_

/**
 * @file
 * @brief <a href="/hw/ip/sram_ctrl/doc/">SRAM Controller</a> Device Interface
 * Functions
 */

/**
 * The SRAM Controller can perform destructive operations on data in memory.
 * These operations invalidate the stack and other data that the C runtime
 * requires. Such functionality has been intentionally left out of this library
 * and will need to be triggered by assembly code that does not require a valid
 * stack or initialized static data. Such functionality includes:
 *
 * - Requesting a new scrambling key.
 * - Initializing the contents of memory.
 *
 * For the same reason there is no accessor function in this library for the
 * `status.ESCALATED` bit. If that bit is set then memory is inaccessible.
 */

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Hardware instantiation parameters for SRAM Controller.
 *
 * This struct describes information about the underlying hardware that is
 * not determined until the hardware design is used as part of a top-level
 * design.
 */
typedef struct dif_sram_ctrl_params {
  /**
   * The base address for the SRAM Controller hardware registers.
   */
  mmio_region_t base_addr;
} dif_sram_ctrl_params_t;

/**
 * A handle to SRAM Controller.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_sram_ctrl {
  dif_sram_ctrl_params_t params;
} dif_sram_ctrl_t;

/**
 * The result of a SRAM Controller operation.
 */
typedef enum dif_sram_ctrl_result {
  /**
   * Indicates that the operation succeeded.
   */
  kDifSramCtrlOk = 0,
  /**
   * Indicates some unspecified failure.
   */
  kDifSramCtrlError,
  /**
   * Indicates that some parameter passed into a function failed a
   * precondition.
   *
   * When this value is returned, no hardware operations occurred.
   */
  kDifSramCtrlBadArg,
} dif_sram_ctrl_result_t;

/**
 * A toggle state: enabled, or disabled.
 *
 * This enum may be used instead of a `bool` when describing an enabled/disabled
 * state.
 */
typedef enum dif_sram_ctrl_toggle {
  /**
   * The "enabled" state.
   */
  kDifSramCtrlToggleEnabled,
  /**
   * The "disabled" state.
   */
  kDifSramCtrlToggleDisabled,
} dif_sram_ctrl_toggle_t;

/**
 * Creates a new handle for SRAM Controller.
 *
 * This function does not actuate the hardware.
 *
 * @param params Hardware instantiation parameters.
 * @param[out] handle Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_sram_ctrl_result_t dif_sram_ctrl_init(dif_sram_ctrl_params_t params,
                                          dif_sram_ctrl_t *handle);

/**
 * Trigger one alert event.
 *
 * @param sram_ctrl A SRAM Controller handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_sram_ctrl_result_t dif_sram_ctrl_force_alert(
    const dif_sram_ctrl_t *sram_ctrl);

/**
 * Lock execution enable register.
 *
 * This function prevents any further writes to the
 * execution enable register. Future attempts to enable or disable
 * execution from SRAM will fail.
 *
 * @param sram_ctrl A SRAM Controller handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_sram_ctrl_result_t dif_sram_ctrl_exec_lock(
    const dif_sram_ctrl_t *sram_ctrl);

/**
 * Reports whether the execution enable register is locked or not.
 *
 * If the execution enable register is locked then it is no longer possible to
 * enable or disable execution from SRAM.
 *
 * @param sram_ctrl A SRAM Controller handle.
 * @param state[out] Enabled if locked, disabled if unlocked.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_sram_ctrl_result_t dif_sram_ctrl_exec_is_locked(
    const dif_sram_ctrl_t *sram_ctrl, dif_sram_ctrl_toggle_t *state);

/**
 * Reports whether the control register is locked or not.
 *
 * If the control register is locked then it is no longer possible to request a
 * new scrambling key.
 *
 * @param sram_ctrl A SRAM Controller handle.
 * @param state[out] Enabled if locked, disabled if unlocked.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_sram_ctrl_result_t dif_sram_ctrl_control_is_locked(
    const dif_sram_ctrl_t *sram_ctrl, dif_sram_ctrl_toggle_t *state);

/**
 * The result of an attempt to enable or disable execution from SRAM.
 */
typedef enum dif_sram_ctrl_exec_result {
  /**
   * Indicates that the operation succeeded.
   */
  kDifSramCtrlExecOk = kDifSramCtrlOk,
  /**
   * Indicates some unspecified failure.
   */
  kDifSramCtrlExecError = kDifSramCtrlError,
  /**
   * Indicates that some parameter passed into a function failed a
   * precondition.
   *
   * When this value is returned, no hardware operations occured.
   */
  kDifSramCtrlExecBadArg = kDifSramCtrlBadArg,
  /**
   * Indicates that this operation has been locked out, and can never
   * succeed until hardware reset.
   */
  kDifSramCtrlExecLocked,
} dif_sram_ctrl_exec_result_t;

/**
 * Enable or disable execution from SRAM.
 *
 * @param sram_ctrl A SRAM Controller handle.
 * @param state Enable or disable SRAM execution.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_sram_ctrl_exec_result_t dif_sram_ctrl_exec_set_enabled(
    const dif_sram_ctrl_t *sram_ctrl, dif_sram_ctrl_toggle_t state);

/**
 * Report whether execution from SRAM is currently enabled or disabled.
 *
 * @param sram_ctrl A SRAM Controller handle.
 * @param[out] state State of SRAM execution (enabled or disabled).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_sram_ctrl_result_t dif_sram_ctrl_exec_get_enabled(
    const dif_sram_ctrl_t *sram_ctrl, dif_sram_ctrl_toggle_t *state);

/**
 * Retrieve the error state from the SRAM controller.
 *
 * This function will return `kDifSramCtrlOk` if the error state of the
 * SRAM controller was successfully fetched regardless of whether the SRAM
 * controller has experienced an uncorrectable parity error or not. The `error`
 * argument must be checked to see if a uncorrectable parity error has actually
 * occurred.
 *
 * @param sram_ctrl A SRAM Controller handle.
 * @param[out] error Whether an uncorrectable parity error has occurred.
 * @param[out] address The byte address of the last parity error (optional).
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_sram_ctrl_result_t dif_sram_ctrl_get_error(const dif_sram_ctrl_t *sram_ctrl,
                                               bool *error, uintptr_t *address);

/**
 * SRAM controller scrambling status.
 */
typedef struct dif_sram_ctrl_scrambling_status {
  /**
   * The validity of the scrambling key. If the key is valid then SRAM is
   * scrambled using a key from OTP. Otherwise SRAM is scrambled using the
   * default all-zero key and nonce.
   */
  bool key_valid;

  /**
   * The validity of the seed used to derive the scrambling key in OTP. If the
   * seed is not valid then the scrambling key was derived using the default
   * all-zero seed.
   */
  bool key_seed_valid;
} dif_sram_ctrl_scrambling_status_t;

/**
 * Retrieve the scrambling status from the SRAM controller.
 *
 * If `key_valid` is set to true then SRAM is scrambled using a valid key from
 * OTP. Otherwise SRAM is scrambled using a default all-zero key and all-zero
 * nonce.
 *
 * @param sram_ctrl A SRAM Controller handle.
 * @param[out] status Information about the scrambling key in use.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_sram_ctrl_result_t dif_sram_ctrl_get_scrambling_status(
    const dif_sram_ctrl_t *sram_ctrl,
    dif_sram_ctrl_scrambling_status_t *status);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SRAM_CTRL_H_
