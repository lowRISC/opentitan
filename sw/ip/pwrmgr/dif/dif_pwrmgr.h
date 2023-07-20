// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PWRMGR_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PWRMGR_H_

/**
 * @file
 * @brief <a href="/hw/ip/pwrmgr/doc/">Power Manager</a> Device Interface
 * Functions
 */

#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "sw/device/lib/dif/autogen/dif_pwrmgr_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * A request type, i.e. wakeup or reset.
 */
typedef enum dif_pwrmgr_req_type {
  /**
   * A wakeup request.
   */
  kDifPwrmgrReqTypeWakeup,
  /**
   * A reset request.
   */
  kDifPwrmgrReqTypeReset,
} dif_pwrmgr_req_type_t;

/**
 * Options for enabling/disabling various clock and power domains
 * in low and active power states.
 *
 * Constants below are bitmasks that can be combined to define configurations.
 *
 * See also: `dif_pwrmgr_domain_config_t`.
 */
typedef enum dif_pwrmgr_domain_option {
  /**
   * Enable core clock in low power state.
   */
  kDifPwrmgrDomainOptionCoreClockInLowPower = (1u << 0),
  /**
   * Enable input/output (IO) clock in low power state.
   */
  kDifPwrmgrDomainOptionIoClockInLowPower = (1u << 1),
  /**
   * Enable USB clock in low power state.
   */
  kDifPwrmgrDomainOptionUsbClockInLowPower = (1u << 2),
  /**
   * Enable USB clock in active power state.
   */
  kDifPwrmgrDomainOptionUsbClockInActivePower = (1u << 3),
  /**
   * Enable main power domain in low power state.
   */
  kDifPwrmgrDomainOptionMainPowerInLowPower = (1u << 4),
} dif_pwrmgr_domain_option_t;

/**
 * A set of domain options.
 *
 * This type is used for specifying and querying which clock and power domains
 * are enabled in low and active power states.
 *
 * See also: `dif_pwrmgr_domain_option_t`.
 */
typedef uint8_t dif_pwrmgr_domain_config_t;

/**
 * A wakeup request source.
 *
 * Constants below are bitmasks that can be used to define sets of wakeup
 * request sources.
 *
 * See also: `dif_pwrmgr_request_sources_t`.
 *
 * Note: This needs to be updated once the HW is finalized.
 */
typedef enum dif_pwrmgr_wakeup_request_source {
  kDifPwrmgrWakeupRequestSourceOne = (1u << 0),
  kDifPwrmgrWakeupRequestSourceTwo = (1u << 1),
  kDifPwrmgrWakeupRequestSourceThree = (1u << 2),
  kDifPwrmgrWakeupRequestSourceFour = (1u << 3),
  kDifPwrmgrWakeupRequestSourceFive = (1u << 4),
  kDifPwrmgrWakeupRequestSourceSix = (1u << 5),
} dif_pwrmgr_wakeup_request_source_t;

/**
 * A reset request source.
 *
 * Constants below are bitmasks that can be used to define sets of reset
 * request sources.
 *
 * See also: `dif_pwrmgr_request_sources_t`.
 *
 * Note: This needs to be updated once the HW is finalized.
 */
typedef enum dif_pwrmgr_reset_request_source {
  kDifPwrmgrResetRequestSourceOne = (1u << 0),
  kDifPwrmgrResetRequestSourceTwo = (1u << 1),
} dif_pwrmgr_reset_request_source_t;

/**
 * A set of request sources.
 *
 * This type is used for specifying which request sources are enabled for a
 * particular request type, i.e. wakeup or reset, as well querying wakeup
 * reasons.
 *
 * See also: `dif_pwrmgr_wakeup_request_source_t`,
 * `dif_pwrmgr_reset_request_source_t`.
 */
typedef uint32_t dif_pwrmgr_request_sources_t;

/**
 * A wakeup type.
 *
 * Constants below are bitmasks that can be used to define sets of wakeup types.
 *
 * See also: `dif_pwrmgr_wakeup_types_t`.
 */
typedef enum dif_pwrmgr_wakeup_type {
  /**
   * Wakeup due to a peripheral request.
   */
  kDifPwrmgrWakeupTypeRequest = (1u << 0),
  /**
   * Despite low power mode being enabled and executing a wait for interrupt
   * (WFI) instruction, an interrupt arrived at just the right time to break the
   * executing core out of WFI.
   */
  kDifPwrmgrWakeupTypeFallThrough = (1u << 1),
  /**
   * Despite low power mode being enabled and executing a wait for interrupt
   * (WFI) instruction, an active flash, life cycle, or OTP operation was
   * in progress when the power controller attempted to initiate low power
   * entry.
   */
  kDifPwrmgrWakeupTypeAbort = (1u << 2),
} dif_pwrmgr_wakeup_type_t;

/**
 * A set of wakeup types.
 *
 * See also: `dif_pwrmgr_wakeup_type_t`.
 */
typedef uint8_t dif_pwrmgr_wakeup_types_t;

typedef enum dif_pwrmgr_fatal_err_type {
  /**
   * A fatal error for regfile integrity.
   */
  kDifPwrmgrFatalErrTypeRegfileIntegrity = 1u << 0,
  /**
   * A fatal error for escalation timeout.
   */
  kDifPwrmgrFatalErrTypeEscalationTimeout = 1u << 1,
  /**
   * A fatal error for main power glitch.
   */
  kDifPwrmgrFatalErrTypeMainPowerGlitch = 1u << 2,
} dif_pwrmgr_fatal_err_type_t;

/**
 * A set of fatal errors.
 *
 * This type is used to read the fatal error codes.
 */
typedef uint32_t dif_pwrmgr_fatal_err_codes_t;

/**
 * Wakeup types and requests from sources since the last time recording started.
 */
typedef struct dif_pwrmgr_wakeup_reason {
  /**
   * Wakeup types since the last time recording started.
   */
  dif_pwrmgr_wakeup_types_t types;
  /**
   * Sources that requested wakeup since the last time recording started.
   */
  dif_pwrmgr_request_sources_t request_sources;
} dif_pwrmgr_wakeup_reason_t;

/**
 * Enables or disables low power state.
 *
 * When enabled, the power manager transitions to low power state on the next
 * wait for interrupt (WFI) instruction. Since the hardware clears the
 * corresponding bit automatically, this function must be called before each
 * transition to low power state.
 *
 * This function can be configured to skip synchronization to the slow clock
 * domain, under the assumption that timely synchronization will be performed
 * by some of the other functions that can trigger it.
 *
 * @param pwrmgr A power manager handle.
 * @param new_state Whether low power state is enabled.
 * @param sync_state Whether to wait for state to transfer to slow domain
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pwrmgr_low_power_set_enabled(const dif_pwrmgr_t *pwrmgr,
                                              dif_toggle_t new_state,
                                              dif_toggle_t sync_state);

/**
 * Checks whether low power state is enabled.
 *
 * @param pwrmgr A power manager handle.
 * @param[out] cur_state Whether low power state is enabled.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pwrmgr_low_power_get_enabled(const dif_pwrmgr_t *pwrmgr,
                                              dif_toggle_t *cur_state);

/**
 * Configures power manager to enable/disable various clock and power domains in
 * low and active power states.
 *
 * This function can be configured to skip synchronization to the slow clock
 * domain, under the assumption that timely synchronization will be performed
 * by some of the other functions that can trigger it.
 *
 * @param pwrmgr A power manager handle.
 * @param config A domain configuration.
 * @param sync_state Whether to wait for state to transfer to slow domain
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pwrmgr_set_domain_config(const dif_pwrmgr_t *pwrmgr,
                                          dif_pwrmgr_domain_config_t config,
                                          dif_toggle_t sync_state);

/**
 * Gets current power manager configuration.
 *
 * @param pwrmgr A power manager handle.
 * @param[out] config Current configuration.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pwrmgr_get_domain_config(const dif_pwrmgr_t *pwrmgr,
                                          dif_pwrmgr_domain_config_t *config);

/**
 * Sets sources enabled for a request type.
 *
 * A wakeup or reset request can be triggered by multiple sources, e.g. GPIO,
 * watchdog timer, USB, etc. This function sets which sources are enabled for a
 * particular request type.
 *
 * This function can be configured to skip synchronization to the slow clock
 * domain, under the assumption that timely synchronization will be performed
 * by some of the other functions that can trigger it.
 *
 * @param pwrmgr A power manager handle.
 * @param req_type A request type.
 * @param sources Sources enabled for the given request type.
 * @param sync_state Whether to wait for state to transfer to slow domain
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pwrmgr_set_request_sources(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_req_type_t req_type,
    dif_pwrmgr_request_sources_t sources, dif_toggle_t sync_state);

/**
 * Gets sources enabled for a request type.
 *
 * A wakeup or reset request can be triggered by multiple sources, e.g. GPIO,
 * watchdog timer, USB, etc. This function gets which sources are enabled for a
 * particular request type.
 *
 * @param pwrmgr A power manager handle.
 * @param req_type A request type.
 * @param[out] sources Sources enabled for the given request type.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pwrmgr_get_request_sources(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_req_type_t req_type,
    dif_pwrmgr_request_sources_t *sources);

/**
 * Gets request sources that are currently active for a request type.
 *
 * @param pwrmgr A power manager handle.
 * @param req_type A request type.
 * @param[out] sources Request sources that are currently active for the given
 *                     request type.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pwrmgr_get_current_request_sources(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_req_type_t req_type,
    dif_pwrmgr_request_sources_t *sources);

/**
 * Locks sources of a request type.
 *
 * Once the sources of a particular request type is locked, they cannot be
 * changed until the hardware is reset.
 *
 * @param pwrmgr A power manager handle.
 * @param req_type A request type.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pwrmgr_request_sources_lock(const dif_pwrmgr_t *pwrmgr,
                                             dif_pwrmgr_req_type_t req_type);

/**
 * Checks whether sources of a request type is locked.
 *
 * @param pwrmgr A power manager handle.
 * @param req_type A request type.
 * @param[out] is_locked Whether sources of the given request type is locked.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pwrmgr_request_sources_is_locked(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_req_type_t req_type,
    bool *is_locked);

/**
 * Enables or disables recording of wakeup requests.
 *
 * Power manager automatically starts recording wakeup requests when it
 * begins a valid low power entry. Recording continues until it is explicitly
 * disabled by calling this function.
 *
 * @param pwrmgr A power manager handle.
 * @param new_state Whether wakeup requests should be recorded.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pwrmgr_wakeup_request_recording_set_enabled(
    const dif_pwrmgr_t *pwrmgr, dif_toggle_t new_state);

/**
 * Checks whether wakeup requests are being recorded.
 *
 * @param pwrmgr A power manager handle.
 * @param[out] cur_state Whether wakeup requests are being recorded.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pwrmgr_wakeup_request_recording_get_enabled(
    const dif_pwrmgr_t *pwrmgr, dif_toggle_t *cur_state);

/**
 * Gets wakeup reason and source requests since the last time recording
 * started.
 *
 * Power manager automatically starts recording wakeup requests when it
 * begins a valid low power entry. Recording continues until it is explicitly
 * disabled by calling `dif_pwrmgr_wakeup_request_recording_set_enabled`. Thus,
 * it is possible to record wakeup requests from multiple sources as well as
 * multiple wakeup types.
 *
 * @param pwrmgr A power manager handle.
 * @param[out] reason Wakeup reasons.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pwrmgr_wakeup_reason_get(const dif_pwrmgr_t *pwrmgr,
                                          dif_pwrmgr_wakeup_reason_t *reason);

/**
 * Clears wakeup reason(s) recorded since the last time recording started.
 *
 * @param pwrmgr A power manager handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pwrmgr_wakeup_reason_clear(const dif_pwrmgr_t *pwrmgr);

/**
 * Read the fatal error codes.
 *
 * @param pwrmgr Power Manager Handle.
 * @param[out] codes The fatal error codes.
 * @returns The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_pwrmgr_fatal_err_code_get_codes(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_fatal_err_codes_t *codes);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PWRMGR_H_
