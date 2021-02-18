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

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_warn_unused_result.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Enumeration for enabling/disabling various functionality.
 */
typedef enum dif_pwrmgr_toggle {
  /**
   * Enabled state.
   */
  kDifPwrmgrToggleEnabled,
  /**
   * Disabled state.
   */
  kDifPwrmgrToggleDisabled,
} dif_pwrmgr_toggle_t;

/**
 * Hardware instantiation parameters for power manager.
 *
 * This struct describes information about the underlying hardware that is
 * not determined until the hardware design is used as part of a top-level
 * design.
 */
typedef struct dif_pwrmgr_params {
  /**
   * Base address of power manager registers.
   */
  mmio_region_t base_addr;
} dif_pwrmgr_params_t;

/**
 * A handle to power manager.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_pwrmgr {
  /**
   * Hardware instantiation parameters.
   */
  dif_pwrmgr_params_t params;
} dif_pwrmgr_t;

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
 * Result of a power manager operation.
 */
typedef enum dif_pwrmgr_result {
  /**
   * The call succeeded.
   */
  kDifPwrmgrOk = 0,
  /**
   * A non-specific error occurred and the hardware is in an invalid or
   * irrecoverable state.
   */
  kDifPwrmgrError = 1,
  /**
   * The caller supplied invalid arguments but the call did not cause any
   * side-effects and the hardware is in a valid and recoverable state.
   */
  kDifPwrmgrBadArg = 2,
} dif_pwrmgr_result_t;

/**
 * Result of a power manager operation that writes to lockable configuration
 * registers.
 */
typedef enum dif_pwrmgr_config_result {
  /**
   * The call succeeded.
   */
  kDifPwrmgrConfigOk = kDifPwrmgrOk,
  /**
   * A non-specific error occurred and the hardware is in an invalid or
   * irrecoverable state.
   */
  kDifPwrmgrConfigError = kDifPwrmgrError,
  /**
   * The caller supplied invalid arguments but the call did not cause any
   * side-effects and the hardware is in a valid and recoverable state.
   */
  kDifPwrmgrConfigBadArg = kDifPwrmgrBadArg,
  /**
   * The register that needs to be written to is locked.
   */
  kDifPwrMgrConfigLocked,
} dif_pwrmgr_config_result_t;

/**
 * Power manager interrupts.
 */
typedef enum dif_pwrmgr_irq {
  /**
   * The device woke up from low power state.
   *
   * Note: This interrupt is not triggered during power-on reset.
   */
  kDifPwrmgrIrqWakeup = 0,
  /**
   * \internal Last power manager interrupt.
   */
  kDifPwrmgrIrqLast = kDifPwrmgrIrqWakeup,
} dif_pwrmgr_irq_t;

/**
 * A snapshot of the enablement state of power manager interrupts.
 *
 * This is an opaque type, to be used with the `dif_pwrmgr_irq_disable_all()`
 * and `dif_pwrmgr_irq_restore_all()` functions.
 */
typedef uint32_t dif_pwrmgr_irq_snapshot_t;

/**
 * Creates a new handle for power manager.
 *
 * This function does not actuate the hardware.
 *
 * @param params Hardware instantiation parameters.
 * @param[out] pwrmgr Out-param for the initialized handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_pwrmgr_result_t dif_pwrmgr_init(dif_pwrmgr_params_t params,
                                    dif_pwrmgr_t *pwrmgr);

/**
 * Enables or disables low power state.
 *
 * When enabled, the power manager transitions to low power state on the next
 * wait for interrupt (WFI) instruction. Since the hardware clears the
 * corresponding bit automatically, this function must be called before each
 * transition to low power state.
 *
 * Note: This function also syncs changes to the slow clock domain for them to
 * take effect.
 *
 * @param pwrmgr A power manager handle.
 * @param new_state Whether low power state is enabled.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_pwrmgr_config_result_t dif_pwrmgr_low_power_set_enabled(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_toggle_t new_state);

/**
 * Checks whether low power state is enabled.
 *
 * @param pwrmgr A power manager handle.
 * @param[out] cur_state Whether low power state is enabled.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_pwrmgr_result_t dif_pwrmgr_low_power_get_enabled(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_toggle_t *cur_state);

/**
 * Configures power manager to enable/disable various clock and power domains in
 * low and active power states.
 *
 * Note: This function also syncs changes to the slow clock domain for them to
 * take effect.
 *
 * @param pwrmgr A power manager handle.
 * @param config A domain configuration.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_pwrmgr_config_result_t dif_pwrmgr_set_domain_config(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_domain_config_t config);

/**
 * Gets current power manager configuration.
 *
 * @param pwrmgr A power manager handle.
 * @param[out] config Current configuration.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_pwrmgr_result_t dif_pwrmgr_get_domain_config(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_domain_config_t *config);

/**
 * Sets sources enabled for a request type.
 *
 * A wakeup or reset request can be triggered by multiple sources, e.g. GPIO,
 * watchdog timer, USB, etc. This function sets which sources are enabled for a
 * particular request type.
 *
 * Note: This function also syncs changes to the slow clock domain for them to
 * take effect.
 *
 * @param pwrmgr A power manager handle.
 * @param req_type A request type.
 * @param sources Sources enabled for the given request type.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_pwrmgr_config_result_t dif_pwrmgr_set_request_sources(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_req_type_t req_type,
    dif_pwrmgr_request_sources_t sources);

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
DIF_WARN_UNUSED_RESULT
dif_pwrmgr_result_t dif_pwrmgr_get_request_sources(
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
DIF_WARN_UNUSED_RESULT
dif_pwrmgr_result_t dif_pwrmgr_get_current_request_sources(
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
DIF_WARN_UNUSED_RESULT
dif_pwrmgr_result_t dif_pwrmgr_request_sources_lock(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_req_type_t req_type);

/**
 * Checks whether sources of a request type is locked.
 *
 * @param pwrmgr A power manager handle.
 * @param req_type A request type.
 * @param[out] is_locked Whether sources of the given request type is locked.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_pwrmgr_result_t dif_pwrmgr_request_sources_is_locked(
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
DIF_WARN_UNUSED_RESULT
dif_pwrmgr_result_t dif_pwrmgr_wakeup_request_recording_set_enabled(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_toggle_t new_state);

/**
 * Checks whether wakeup requests are being recorded.
 *
 * @param pwrmgr A power manager handle.
 * @param[out] cur_state Whether wakeup requests are being recorded.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_pwrmgr_result_t dif_pwrmgr_wakeup_request_recording_get_enabled(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_toggle_t *cur_state);

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
DIF_WARN_UNUSED_RESULT
dif_pwrmgr_result_t dif_pwrmgr_wakeup_reason_get(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_wakeup_reason_t *reason);

/**
 * Clears wakeup reason(s) recorded since the last time recording started.
 *
 * @param pwrmgr A power manager handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_pwrmgr_result_t dif_pwrmgr_wakeup_reason_clear(const dif_pwrmgr_t *pwrmgr);

/**
 * Returns whether a particular interrupt is currently pending.
 *
 * @param pwrmgr A power manager handle.
 * @param irq An interrupt type.
 * @param[out] is_pending Out-param for whether the interrupt is pending.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_pwrmgr_result_t dif_pwrmgr_irq_is_pending(const dif_pwrmgr_t *pwrmgr,
                                              dif_pwrmgr_irq_t irq,
                                              bool *is_pending);

/**
 * Acknowledges a particular interrupt, indicating to the hardware that it has
 * been successfully serviced.
 *
 * @param pwrmgr A power manager handle.
 * @param irq An interrupt type.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_pwrmgr_result_t dif_pwrmgr_irq_acknowledge(const dif_pwrmgr_t *pwrmgr,
                                               dif_pwrmgr_irq_t irq);

/**
 * Checks whether a particular interrupt is currently enabled or disabled.
 *
 * @param pwrmgr A power manager handle.
 * @param irq An interrupt type.
 * @param[out] state Out-param toggle state of the interrupt.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_pwrmgr_result_t dif_pwrmgr_irq_get_enabled(const dif_pwrmgr_t *pwrmgr,
                                               dif_pwrmgr_irq_t irq,
                                               dif_pwrmgr_toggle_t *state);

/**
 * Sets whether a particular interrupt is currently enabled or disabled.
 *
 * @param pwrmgr A power manager handle.
 * @param irq An interrupt type.
 * @param state The new toggle state for the interrupt.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_pwrmgr_result_t dif_pwrmgr_irq_set_enabled(const dif_pwrmgr_t *pwrmgr,
                                               dif_pwrmgr_irq_t irq,
                                               dif_pwrmgr_toggle_t state);

/**
 * Forces a particular interrupt, causing it to be serviced as if hardware had
 * asserted it.
 *
 * @param pwrmgr A power manager handle.
 * @param irq An interrupt type.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_pwrmgr_result_t dif_pwrmgr_irq_force(const dif_pwrmgr_t *pwrmgr,
                                         dif_pwrmgr_irq_t irq);

/**
 * Disables all interrupts, optionally snapshotting all toggle state for later
 * restoration.
 *
 * @param pwrmgr A power manager handle.
 * @param[out] snapshot Out-param for the snapshot; may be `NULL`.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_pwrmgr_result_t dif_pwrmgr_irq_disable_all(
    const dif_pwrmgr_t *pwrmgr, dif_pwrmgr_irq_snapshot_t *snapshot);

/**
 * Restores interrupts from the given snapshot.
 *
 * This function can be used with `dif_pwrmgr_irq_disable_all()` to temporary
 * interrupt save-and-restore.
 *
 * @param pwrmgr A power manager handle.
 * @param snapshot A snapshot to restore from.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_pwrmgr_result_t dif_pwrmgr_irq_restore_all(
    const dif_pwrmgr_t *pwrmgr, const dif_pwrmgr_irq_snapshot_t *snapshot);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_PWRMGR_H_
