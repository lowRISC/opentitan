// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_LC_CTRL_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_LC_CTRL_H_

/**
 * @file
 * @brief <a href="/hw/ip/lc_ctrl/doc/">Lifecycle Controller</a> Device
 * Interface Functions
 */

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_warn_unused_result.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * A lifecycle controller status code.
 *
 * See `dif_lc_ctrl_get_status()`.
 */
typedef enum dif_lc_ctrl_status_code {
  /**
   * Indicates that the controller has been successfully initialized.
   */
  kDifLcCtrlStatusCodeReady,
  /**
   * Indicates that the last lifecycle transition succeeded.
   */
  kDifLcCtrlStatusCodeSuccess,
  /**
   * Indicates that too many hardware transitions have occured, and the hardware
   * will not transition the lifecycle any further.
   */
  kDifLcCtrlStatusCodeTooManyTransitions,
  /**
   * Indicates that an invalid lifecycle transition was attempted.
   */
  kDifLcCtrlStatusCodeInvalidTransition,
  /**
   * Indicates that a bad token was supplied for conditional transition.
   */
  kDifLcCtrlStatusCodeBadToken,
  /**
   * Indicates an error during an OTP operation.
   *
   * This error will raise an alert.
   */
  kDifLcCtrlStatusCodeOtpError,
  /**
   * Indicates an error in the controller's internal state.
   *
   * This error will raise an alert.
   */
  kDifLcCtrlStatusCodeCorrupt,
} dif_lc_ctrl_status_code_t;

/**
 * A bit-vector of `dif_lc_ctrl_status_code_t`s.
 *
 * Whether a particular status is contained in this vector can be discovered by
 * using it as a bit index: `bitfield_bit32_read(status, status_code);`.
 */
typedef uint32_t dif_lc_ctrl_status_t;

/**
 * A lifecycle state.
 *
 * This enum represents all states that the lifecycle state register can be in;
 * some of these do not correspond to "real" lifecycle states, and cannot be
 * transitioned to.
 */
typedef enum dif_lc_ctrl_state_t {
  /**
   * The initial post-manufacture state.
   *
   * All functions are disabled.
   */
  kDifLcCtrlStateRaw,
  /**
   * The zeroth test state.
   *
   * Debug functions are enabled.
   */
  kDifLcCtrlStateTestUnlocked0,
  /**
   * The zeroth locked test state.
   *
   * All functions are disabled.
   */
  kDifLcCtrlStateTestLocked0,
  /**
   * The first test state.
   *
   * Debug functions are enabled.
   */
  kDifLcCtrlStateTestUnlocked1,
  /**
   * The first locked test state.
   *
   * All functions are disabled.
   */
  kDifLcCtrlStateTestLocked1,
  /**
   * The second test state.
   *
   * Debug functions are enabled.
   */
  kDifLcCtrlStateTestUnlocked2,
  /**
   * The second locked test state.
   *
   * All functions are disabled.
   */
  kDifLcCtrlStateTestLocked2,
  /**
   * The third test state.
   *
   * Debug functions are enabled.
   */
  kDifLcCtrlStateTestUnlocked3,
  /**
   * The development state.
   *
   * Some debug functions are enabled.
   */
  kDifLcCtrlStateDev,
  /**
   * The main production state.
   *
   * No debug functions are enabled.
   */
  kDifLcCtrlStateProd,
  /**
   * The EOL production state.
   *
   * Same as Prod, except Rma cannot be transitioned to.
   */
  kDifLcCtrlStateProdEnd,
  /**
   * RMA manufacturer analysis state.
   */
  kDifLcCtrlStateRma,
  /**
   * The scrap EOL state.
   *
   * Cannot be transitioned from; all functions are disabled.
   */
  kDifLcCtrlStateScrap,

  /**
   * State entered immediately after a transition occurs.
   *
   * Not a real state.
   */
  kDifLcCtrlStatePostTransition,
  /**
   * State entered immediately after an alert is raised.
   *
   * Not a real state.
   */
  kDifLcCtrlStateEscalate,
  /**
   * Indicates that the encoded lifecycle is invalid.
   *
   * Not a real state.
   */
  kDifLcCtrlStateInvalid,
} dif_lc_ctrl_state_t;

/**
 * A personalization state, indicating whether the device has been successfully
 * personalized.
 */
typedef enum dif_lc_ctrl_id_state {
  /**
   * Indicates that the device has not yet been personalized.
   */
  kDifLcCtrlIdStateBlank,
  /**
   * Indicates that the device has been personalized.
   */
  kDifLcCtrlIdStatePersonalized,
  /**
   * Indicates that the personalization state is corrupt.
   */
  kDifLcCtrlIdStateInvalid,
} dif_lc_ctrl_id_state_t;

/**
 * A 128-bit unlock token used for certain kinds of lifecycle transitions.
 */
typedef struct dif_lc_ctrl_token {
  uint8_t data[128 / 8];
} dif_lc_ctrl_token_t;

/**
 * Hardware instantiation parameters for a lifecycle controller.
 *
 * This struct describes information about the underlying hardware that is
 * not determined until the hardware design is used as part of a top-level
 * design.
 */
typedef struct dif_lc_ctrl_params {
  /**
   * The base address for the lifecycle controller hardware registers.
   */
  mmio_region_t base_addr;
} dif_lc_ctrl_params_t;

/**
 * A handle to a lifecycle controller.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_lc_ctrl {
  dif_lc_ctrl_params_t params;
} dif_lc_ctrl_t;

/**
 * The result of a lifecycle controller operation.
 */
typedef enum dif_lc_ctrl_result {
  /**
   * Indicates that the operation succeeded.
   */
  kDifLcCtrlOk = 0,
  /**
   * Indicates some unspecified failure.
   */
  kDifLcCtrlError = 1,
  /**
   * Indicates that some parameter passed into a function failed a
   * precondition.
   *
   * When this value is returned, no hardware operations occured.
   */
  kDifLcCtrlBadArg = 2,
} dif_lc_ctrl_result_t;

/**
 * The result of a lifecycle attempt counter operation.
 */
typedef enum dif_lc_ctrl_attempts_result {
  /**
   * Indicates that the operation succeeded.
   */
  kDifLcCtrlAttemptsOk = kDifLcCtrlOk,
  /**
   * Indicates some unspecified failure.
   */
  kDifLcCtrlAttemptsError = kDifLcCtrlError,
  /**
   * Indicates that some parameter passed into a function failed a
   * precondition.
   *
   * When this value is returned, no hardware operations occured.
   */
  kDifLcCtrlAttemptsBadArg = kDifLcCtrlBadArg,
  /**
   * Indicates that too many lifecycle transitions have occurred, such that the
   * hardware can no longer keep a count.
   */
  kDifLcCtrlAttemptsTooMany,
} dif_lc_ctrl_attempts_result_t;

/**
 * The result of a lifecycle controller operation involving the hardware mutex.
 */
typedef enum dif_lc_ctrl_mutex_result {
  /**
   * Indicates that the operation succeeded.
   */
  kDifLcCtrlMutexOk = kDifLcCtrlOk,
  /**
   * Indicates some unspecified failure.
   */
  kDifLcCtrlMutexError = kDifLcCtrlError,
  /**
   * Indicates that some parameter passed into a function failed a
   * precondition.
   *
   * When this value is returned, no hardware operations occured.
   */
  kDifLcCtrlMutexBadArg = kDifLcCtrlBadArg,

  /**
   * Indicates that a mutex-guarded operation failed because someone (other
   * than software) is holding it.
   */
  kDifLcCtrlMutexAlreadyTaken = 3,
} dif_lc_ctrl_mutex_result_t;

/**
 * An alert that can be raised by the hardware.
 */
typedef enum dif_lc_ctrl_alert {
  /**
   * The alert triggered by a `kDifLcCtrlStatusCodeOtpError`.
   */
  kDifLcCtrlAlertOtp,
  /**
   * The alert triggered by a `kDifLcCtrlStatusCodeCorrupt`.
   */
  kDifLcCtrlAlertCorrupt,
} dif_lc_ctrl_alert_t;

/**
 * Creates a new handle for the lifecycle controller.
 *
 * This function does not actuate the hardware.
 *
 * @param params Hardware instantiation parameters.
 * @param[out] lc Out param for the initialized handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_lc_ctrl_result_t dif_lc_ctrl_init(dif_lc_ctrl_params_t params,
                                      dif_lc_ctrl_t *lc);

/**
 * Returns the current state of the lifecycle controller.
 *
 * @param lc A lifecycle handle.
 * @param[out] state Out-param for the controller's state.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_lc_ctrl_result_t dif_lc_ctrl_get_state(const dif_lc_ctrl_t *lc,
                                           dif_lc_ctrl_state_t *state);

/**
 * Returns the number of lifecycle transitions that this device has attempted,
 * up to 16.
 *
 * @param lc A lifecycle handle.
 * @param[out] state Out-param for the controller's state.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_lc_ctrl_attempts_result_t dif_lc_ctrl_get_attempts(const dif_lc_ctrl_t *lc,
                                                       uint8_t *count);

/**
 * Returns the current status of the lifecycle controller.
 *
 * @param lc A lifecycle handle.
 * @param[out] status Out-param for the controller's status.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_lc_ctrl_result_t dif_lc_ctrl_get_status(const dif_lc_ctrl_t *lc,
                                            dif_lc_ctrl_status_t *status);

/**
 * Returns the current personalization state of the lifecycle controller.
 *
 * @param lc A lifecycle handle.
 * @param[out] state Out-param for the controller's personalization state.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_lc_ctrl_result_t dif_lc_ctrl_get_id_state(const dif_lc_ctrl_t *lc,
                                              dif_lc_ctrl_id_state_t *state);

/**
 * Forces a particular alert, causing it to be escalated as if the hardware had
 * raised it.
 *
 * @param lc A lifecycle handle.
 * @param alert The alert to force.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_lc_ctrl_result_t dif_lc_ctrl_alert_force(const dif_lc_ctrl_t *lc,
                                             dif_lc_ctrl_alert_t alert);

/**
 * Attempts to acquire the lifecycle controller's HW mutex.
 *
 * Returns `kDifLcCtrlMutexHeld` if acquisition fails. It is recommended to
 * call this function in a busy loop to acquire the mutex.
 *
 * @param lc A lifecycle handle.
 * @return The result of the operation.
 */
// Open Q: do we want to be checking REGWEN for all operations dependent on the
// mutex?
DIF_WARN_UNUSED_RESULT
dif_lc_ctrl_mutex_result_t dif_lc_ctrl_mutex_try_acquire(
    const dif_lc_ctrl_t *lc);

/**
 * Releases the lifecycle controller's HW mutex.
 *
 * Calls to this function must be sequenced with successful calls to
 * `dif_lc_ctrl_mutex_try_acquire()`.
 *
 * @param lc A lifecycle handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_lc_ctrl_mutex_result_t dif_lc_ctrl_mutex_release(const dif_lc_ctrl_t *lc);

/**
 * Performs a lifecycle transition.
 *
 * Note that not all transitions require an unlock token; in that case, NULL
 * should be passed as the token.
 *
 * @param lc A lifecycle handle.
 * @param state The state to transition to.
 * @param token A token for unlocking the transition; may be null.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_lc_ctrl_mutex_result_t dif_lc_ctrl_transition(
    const dif_lc_ctrl_t *lc, dif_lc_ctrl_state_t state,
    const dif_lc_ctrl_token_t *token);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_LC_CTRL_H_
