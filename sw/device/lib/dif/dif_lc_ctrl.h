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

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "sw/device/lib/dif/autogen/dif_lc_ctrl_autogen.h"

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
  kDifLcCtrlStatusCodeInitialized,
  /**
   * Indicates that the controller has been successfully initialized
   * and is ready to accept a life cycle transition command.
   */
  kDifLcCtrlStatusCodeReady,
  /**
   * Indicates that the clock manager has successfully switched to the
   * external clock.
   */
  kDifLcCtrlStatusExtClockSwitched,
  /**
   * Indicates that the last lifecycle transition succeeded.
   */
  kDifLcCtrlStatusCodeSuccess,
  /**
   * Indicates that too many hardware transitions have occurred, and the
   * hardware will not transition the lifecycle any further.
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
   * Indicates a flash RMA request error.
   */
  kDifLcCtrlStatusCodeFlashRmaError,
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
  /**
   * Indicates a bus integrity error.
   *
   * This error will raise an alert.
   */
  kDifLcCtrlStatusCodeBusIntegError,
  /**
   * Indicates an ECC error in the lifecycle OTP partition.
   */
  kDifLcCtrlStatusCodeOtpPartError,
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
typedef enum dif_lc_ctrl_state {
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
   * The third locked test state.
   *
   * All functions are disabled.
   */
  kDifLcCtrlStateTestLocked3,
  /**
   * The fourth test state.
   *
   * Debug functions are enabled.
   */
  kDifLcCtrlStateTestUnlocked4,
  /**
   * The fourth locked test state.
   *
   * All functions are disabled.
   */
  kDifLcCtrlStateTestLocked4,
  /**
   * The fifth test state.
   *
   * Debug functions are enabled.
   */
  kDifLcCtrlStateTestUnlocked5,
  /**
   * The fifth locked test state.
   *
   * All functions are disabled.
   */
  kDifLcCtrlStateTestLocked5,
  /**
   * The sixth test state.
   *
   * Debug functions are enabled.
   */
  kDifLcCtrlStateTestUnlocked6,
  /**
   * The sixth locked test state.
   *
   * All functions are disabled.
   */
  kDifLcCtrlStateTestLocked6,
  /**
   * The seventh test state.
   *
   * Debug functions are enabled.
   */
  kDifLcCtrlStateTestUnlocked7,
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
 * A 32-bit hardware revision number.
 */
typedef struct {
  uint16_t silicon_creator_id;
  uint16_t product_id;
  uint8_t revision_id;
} dif_lc_ctrl_hw_rev_t;

/**
 * A 256-bit device id stored in OTP's hw_cfg partition.
 */
typedef struct dif_lc_ctrl_device_id {
  uint32_t data[256 / 32];
} dif_lc_ctrl_device_id_t;

/**
 * Returns the current state of the lifecycle controller.
 *
 * @param lc A lifecycle handle.
 * @param[out] state Out-param for the controller's state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_lc_ctrl_get_state(const dif_lc_ctrl_t *lc,
                                   dif_lc_ctrl_state_t *state);

/**
 * Returns the number of lifecycle transitions that this device has attempted,
 * up to 16.
 *
 * @param lc A lifecycle handle.
 * @param[out] count Out-param for the number of attempts.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_lc_ctrl_get_attempts(const dif_lc_ctrl_t *lc, uint8_t *count);

/**
 * Returns the current status of the lifecycle controller.
 *
 * @param lc A lifecycle handle.
 * @param[out] status Out-param for the controller's status.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_lc_ctrl_get_status(const dif_lc_ctrl_t *lc,
                                    dif_lc_ctrl_status_t *status);

/**
 * Returns the current personalization state of the lifecycle controller.
 *
 * @param lc A lifecycle handle.
 * @param[out] state Out-param for the controller's personalization state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_lc_ctrl_get_id_state(const dif_lc_ctrl_t *lc,
                                      dif_lc_ctrl_id_state_t *state);

/**
 * Returns the hardware revision number reading from lifecycle controller's
 * hardware revision register.
 *
 * @param lc A lifecycle handle.
 * @param[out] hw_rev Out-param for the hardware revision.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_lc_ctrl_get_hw_rev(const dif_lc_ctrl_t *lc,
                                    dif_lc_ctrl_hw_rev_t *hw_rev);

/**
 * Returns the current device id reading from lifecycle controller's device id
 * registers.
 *
 * @param lc A lifecycle handle.
 * @param[out] device_id Out-param for the device id.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_lc_ctrl_get_device_id(const dif_lc_ctrl_t *lc,
                                       dif_lc_ctrl_device_id_t *device_id);

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
OT_WARN_UNUSED_RESULT
dif_result_t dif_lc_ctrl_mutex_try_acquire(const dif_lc_ctrl_t *lc);

/**
 * Releases the lifecycle controller's HW mutex.
 *
 * Calls to this function must be sequenced with successful calls to
 * `dif_lc_ctrl_mutex_try_acquire()`.
 *
 * @param lc A lifecycle handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_lc_ctrl_mutex_release(const dif_lc_ctrl_t *lc);

/**
 * Configures the lifecycle controller to perform a transition.
 *
 * Note that not all transitions require an unlock token; in that case, NULL
 * should be passed as the token.
 *
 * @param lc A lifecycle handle.
 * @param state The state to transition to.
 * @param use_ext_clock Whether to use the external clock for the transition.
 * @param token A token for unlocking the transition; may be null.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_lc_ctrl_configure(const dif_lc_ctrl_t *lc,
                                   dif_lc_ctrl_state_t target_state,
                                   bool use_ext_clock,
                                   const dif_lc_ctrl_token_t *token);

/**
 * Performs a lifecycle transition.
 *
 * @param lc A lifecycle handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_lc_ctrl_transition(const dif_lc_ctrl_t *lc);

/**
 * Writes settings to the vendor-specific OTP test control register.
 *
 * This returns `kDifUnavailable` if the mutex has not been acquired.
 *
 * @param lc A lifecycle handle.
 * @param settings The settings to write to the register.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_lc_ctrl_set_otp_vendor_test_reg(const dif_lc_ctrl_t *lc,
                                                 uint32_t settings);

/**
 * Reads settings from the vendor-specific OTP test control register.
 *
 * This returns `kDifUnavailable` if the mutex has not been acquired.
 *
 * @param lc A lifecycle handle.
 * @param settings Output parameter for the settings.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_lc_ctrl_get_otp_vendor_test_reg(const dif_lc_ctrl_t *lc,
                                                 uint32_t *settings);

/**
 * Clears LC_CTRL_CLAIM_TRANSITION_IF_REGWEN to lock ability to claim mutex over
 * TL-UL, effectively disabling SW-initiated lifecycle transitions.
 *
 * @param lc A lifecycle handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_lc_ctrl_sw_mutex_lock(const dif_lc_ctrl_t *lc);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_LC_CTRL_H_
