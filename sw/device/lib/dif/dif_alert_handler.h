// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_ALERT_HANDLER_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_ALERT_HANDLER_H_

/**
 * @file
 * @brief <a href="/hw/ip/alert_handler/doc/">Alert handler</a> Device Interface
 * Functions
 */

#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_warn_unused_result.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * A toggle state: enabled, or disabled.
 *
 * This enum may be used instead of a `bool` when describing an enabled/disabled
 * state.
 */
typedef enum dif_alert_handler_toggle {
  /**
   * The "enabled" state.
   */
  kDifAlertHandlerToggleEnabled,
  /**
   * The "disabled" state.
   */
  kDifAlertHandlerToggleDisabled,
} dif_alert_handler_toggle_t;

/**
 * Hardware instantiation parameters for the alert handler.
 *
 * This struct describes information about the underlying hardware that is
 * not determined until the hardware design is used as part of a top-level
 * design.
 */
typedef struct dif_alert_handler_params {
  /**
   * The base address for the alert handler hardware registers.
   */
  mmio_region_t base_addr;
  /**
   * The configured number of alerts.
   *
   * This value is fixed by the hardware, but not known to this library.
   */
  uint32_t alert_count;
  /**
   * The configured number of escalation signals.
   *
   * This value is fixed by the hardware, but not known to this library.
   */
  // It's actually fixed at 4 right now but this is likely to become
  // configurable too.
  uint32_t escalation_signal_count;
} dif_alert_handler_params_t;

/**
 * A handle to alert handler.
 *
 * This type should be treated as opaque by users.
 */
typedef struct dif_alert_handler {
  dif_alert_handler_params_t params;
} dif_alert_handler_t;

/**
 * The result of an alert handler operation.
 */
typedef enum dif_alert_handler_result {
  /**
   * Indicates that the operation succeeded.
   */
  kDifAlertHandlerOk = 0,
  /**
   * Indicates some unspecified failure.
   */
  kDifAlertHandlerError = 1,
  /**
   * Indicates that some parameter passed into a function failed a
   * precondition.
   *
   * When this value is returned, no hardware operations occurred.
   */
  kDifAlertHandlerBadArg = 2,
} dif_alert_handler_result_t;

/**
 * The result of an alert handler configuration operation.
 */
typedef enum dif_alert_handler_config_result {
  /**
   * Indicates that the operation succeeded.
   */
  kDifAlertHandlerConfigOk = kDifAlertHandlerOk,
  /**
   * Indicates some unspecified failure.
   */
  kDifAlertHandlerConfigError = kDifAlertHandlerError,
  /**
   * Indicates that some parameter passed into a function failed a
   * precondition.
   *
   * When this value is returned, no hardware operations occurred.
   */
  kDifAlertHandlerConfigBadArg = kDifAlertHandlerBadArg,
  /**
   * Indicates that this operation has been locked out, and can never
   * succeed until hardware reset.
   */
  kDifAlertHandlerConfigLocked = 3,
} dif_alert_handler_config_result_t;

/**
 * An alert class.
 *
 * An alert class roughly specifies how to deal with an alert. The class
 * determines which interrupt handler is fired for an alert, as well as the
 * fine-grained details of the escalation policy, for when the processor
 * fails to respond to an alert quickly enough.
 *
 * Alert classes serve as the alert handler's IRQ types. There is one IRQ for
 * each class. Whenever an alert fires, the corresponding class's IRQ is
 * serviced by the processor (if enabled).
 */
typedef enum dif_alert_handler_class {
  /**
   * Alert class "A".
   */
  kDifAlertHandlerClassA = 0,
  /**
   * Alert class "B".
   */
  kDifAlertHandlerClassB = 1,
  /**
   * Alert class "C".
   */
  kDifAlertHandlerClassC = 2,
  /**
   * Alert class "D".
   */
  kDifAlertHandlerClassD = 3,
} dif_alert_handler_class_t;

/**
 * A snapshot of the enablement state of the interrupts for alert handler.
 *
 * This is an opaque type, to be used with the
 * `dif_alert_handler_irq_disable_all()` and
 * `dif_alert_handler_irq_restore_all()` functions.
 */
typedef uint32_t dif_alert_handler_irq_snapshot_t;

/**
 * An alert, identified by a numeric id.
 *
 * Alerts are hardware-level events indicating that something catastrophic
 * has happened. An alert handler handle.consumes alerts, classifies them to a
 * particular `dif_alert_handler_class_t`, and uses policy information attached
 * to that class to handle it.
 *
 * The number of alerts is configurable at hardware-synthesis time, and is
 * specified by the software when initializing a `dif_alert_handler_t`.
 */
typedef uint32_t dif_alert_handler_alert_t;

/**
 * A local alert originating from within the alert handler itself.
 *
 * A local alert is exactly the same as a normal `dif_alert_handler_alert_t`,
 * except that they use different functions for setting up classification and
 * for getting causes.
 */
typedef enum dif_alert_handler_local_alert {
  kDifAlertHandlerLocalAlertAlertPingFail,
  kDifAlertHandlerLocalAlertEscalationPingFail,
  kDifAlertHandlerLocalAlertAlertIntegrityFail,
  kDifAlertHandlerLocalAlertEscalationIntegrityFail,
} dif_alert_handler_local_alert_t;

/**
 * An escalation signal, identified by a numeric id.
 *
 * An escalation signal is a generic "response" to failing to handle a
 * catastrophic event. What each signal means is determined by the chip.
 *
 * A `dif_alert_handler_class_t` can be configured to raise escalation signals
 * as part of its policy.
 */
typedef uint32_t dif_alert_handler_signal_t;

/**
 * An alert class state.
 *
 * This enum describes the sequence of states in the *escalation protocol*,
 * which triggers under two different conditions:
 * - If too many alerts of a particular class accumualte.
 * - If the software IRQ handler for that class times out.
 *
 * When either of these conditions is reached, phase 0 begins. This may trigger
 * an escalation signal, and after a configured duration, proceed to phase 1.
 * This process repeats until phase 3 ends, at which point the class enters a
 * "bricked" terminal state, which cannot be exited except by reset.
 *
 * At any point, software may end the escalation protocol by calling
 * `dif_alert_handler_escalation_clear()` (unless clearing is disabled).
 * Successfully calling this function, or clearing the IRQ on time, will reset
 * back to the idle state. Note that this function cannot clear the terminal
 * state; that state can only be cleared by resetting the chip.
 */
typedef enum dif_alert_handler_class_state {
  /**
   * The initial, idle state.
   */
  kDifAlertHandlerClassStateIdle,
  /**
   * The "timeout" state, that is, the IRQ has been fired and the clock is
   * ticking for the processor to handle the alert.
   */
  kDifAlertHandlerClassStateTimeout,

  /**
   * The zeroth escalation phase.
   */
  kDifAlertHandlerClassStatePhase0,
  /**
   * The first escalation phase.
   */
  kDifAlertHandlerClassStatePhase1,
  /**
   * The second escalation phase.
   */
  kDifAlertHandlerClassStatePhase2,
  /**
   * The third escalation phase.
   */
  kDifAlertHandlerClassStatePhase3,

  /**
   * The terminal state. Most configurations will never reach this state, since
   * one of the previous phases will use an escalation signal to reset the
   * device.
   */
  kDifAlertHandlerClassStateTerminal,
} dif_alert_handler_class_state_t;

/**
 * Runtime configuration for responding to a given escalation phase.
 *
 * See `dif_alert_handler_class_config_t`.
 */
typedef struct dif_alert_handler_class_phase_signal {
  /**
   * The phase this configuration describes.
   *
   * It is an error for this to not be one of the `Phase` constants in
   * `dif_alert_handler_class_state_t`.
   */
  dif_alert_handler_class_state_t phase;
  /**
   * The signal that should be triggered when this phase begins.
   */
  dif_alert_handler_signal_t signal;
} dif_alert_handler_class_phase_signal_t;

/**
 * Runtime configuration for the duration of an escalation phase.
 *
 * See `dif_alert_handler_class_config_t`.
 */
typedef struct dif_alert_handler_class_phase_duration {
  /**
   * The phase this configuration describes.
   *
   * It is an error for this to not be one of the `Phase` constants in
   * `dif_alert_handler_class_state_t`.
   */
  dif_alert_handler_class_state_t phase;
  /**
   * The duration of this phase, in cycles.
   */
  uint32_t cycles;
} dif_alert_handler_class_phase_duration_t;

/**
 * Runtime configuration for a particular alert class.
 *
 * This struct describes how a particular alert class should be configured,
 * such as which signals are associated with it, and what options are turned
 * on for the escalation protocol.
 *
 * For each of the pointer/length field pairs below, if the length is zero, the
 * pointer may be `NULL`.
 */
typedef struct dif_alert_handler_class_config {
  /**
   * The class this configuration describes.
   */
  dif_alert_handler_class_t alert_class;

  /**
   * A list of alerts that should be classified as having this class.
   *
   * Each alert in this list will additionally be set as enabled.
   */
  const dif_alert_handler_alert_t *alerts;
  /**
   * The length of the array `alerts`.
   */
  size_t alerts_len;

  /**
   * A list of local that should be classified as having this class.
   *
   * Each local alert in this list will additionally be set as enabled.
   */
  const dif_alert_handler_local_alert_t *local_alerts;
  /**
   * The length of the array `local_alerts`.
   */
  size_t local_alerts_len;

  /**
   * Whether the escalation protocol should be used for this class
   * (i.e., accumulator and timeout based escalation).
   *
   * Class IRQs will still fire regardless of this setting.
   */
  dif_alert_handler_toggle_t use_escalation_protocol;

  /**
   * Whether automatic escalation locking should be used for this class.
   *
   * When enabled, upon beginning the escalation protocol, the hardware will
   * lock
   * the escalation clear bit, so that software cannot stop escalation once it
   * has begun.
   */
  dif_alert_handler_toggle_t automatic_locking;

  /**
   * The threshold for the class accmulator which, when reached, will
   * automatically trigger escalation.
   */
  uint16_t accumulator_threshold;

  /**
   * The number of cycles this class's associated IRQ handler has to acknowledge
   * the IRQ before escalation is triggered.
   *
   * A value of zero disables the timeout.
   */
  uint32_t irq_deadline_cycles;

  /**
   * Signals to associate to each escalation phase.
   *
   * Each escalation phase signal in this list will additionally be set as
   * enabled; phases not listed will have their escalation signals disabled.
   */
  const dif_alert_handler_class_phase_signal_t *phase_signals;
  /**
   * The length of the array `phase_signals`.
   */
  size_t phase_signals_len;

  /**
   * Durations, in cycles, of each escalation phase.
   */
  const dif_alert_handler_class_phase_duration_t *phase_durations;
  /**
   * The length of the array `phase_durations`.
   */
  size_t phase_durations_len;
} dif_alert_handler_class_config_t;

/**
 * Runtime configuration for alert handler.
 *
 * This struct describes runtime information for one-time configuration of the
 * hardware.
 */
typedef struct dif_alert_handler_config {
  /**
   * The alert ping timeout, in cycles.
   *
   * The alert handler will regularly, at random intervals, ping alert
   * sources. If a source fails to respond, a local alert will be raised.
   *
   * The appropriate value will be dependent on all of the clocks involved on
   * a chip.
   *
   * Note that the ping timer won't start until `dif_alert_handler_lock()` is
   * successfully called.
   *
   * This value must fit in 24 bits.
   */
  uint32_t ping_timeout;

  /**
   * A list of alert classes to configure.
   */
  const dif_alert_handler_class_config_t *classes;
  /**
   * The length of the array `classes`.
   */
  size_t classes_len;
} dif_alert_handler_config_t;

/**
 * Creates a new handle for alert handler.
 *
 * This function does not actuate the hardware.
 *
 * @param params Hardware instantiation parameters.
 * @param handler Out param for the initialized handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_alert_handler_result_t dif_alert_handler_init(
    dif_alert_handler_params_t params, dif_alert_handler_t *handler);

/**
 * Configures alert handler with runtime information.
 *
 * This function should need to be called once for the lifetime of `handle`.
 *
 * This operation is lock-protected.
 *
 * @param handler An alert handler handle.
 * @param config Runtime configuration parameters.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_alert_handler_config_result_t dif_alert_handler_configure(
    const dif_alert_handler_t *handler, dif_alert_handler_config_t config);
/**
 * Locks out alert handler configuration functionality.
 *
 * Once locked, `dif_alert_handler_configure()` will return
 * `kDifAlertHandlerConfigLocked`.
 *
 * This operation cannot be undone, and should be performed at the end of
 * configuring the alert handler in early boot.
 *
 * This function is reentrant: calling it while functionality is locked will
 * have no effect and return `kDifAlertHandlerOk`.
 *
 * @param handler An alert handler handle.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_alert_handler_result_t dif_alert_handler_lock(
    const dif_alert_handler_t *handler);

/**
 * Checks whether this alert handler is locked.
 *
 * See `dif_alert_handler_lock()`.
 *
 * @param handler An alert handler handle.
 * @param is_locked Out-param for the locked state.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_alert_handler_result_t dif_alert_handler_is_locked(
    const dif_alert_handler_t *handler, bool *is_locked);

/**
 * Returns whether a particular interrupt is currently pending.
 *
 * @param handler An alert handler handle.
 * @param alert_class An alert class.
 * @param is_pending Out-param for whether the interrupt is pending.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_alert_handler_result_t dif_alert_handler_irq_is_pending(
    const dif_alert_handler_t *handler, dif_alert_handler_class_t alert_class,
    bool *is_pending);

/**
 * Acknowledges a particular interrupt, indicating to the hardware that it has
 * been successfully serviced.
 *
 * @param handler An alert handler handle.
 * @param alert_class An alert class.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_alert_handler_result_t dif_alert_handler_irq_acknowledge(
    const dif_alert_handler_t *handler, dif_alert_handler_class_t alert_class);

/**
 * Checks whether a particular interrupt is currently enabled or disabled.
 *
 * @param handler An alert handler handle.
 * @param alert_class An alert class.
 * @param state Out-param toggle state of the interrupt.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_alert_handler_result_t dif_alert_handler_irq_get_enabled(
    const dif_alert_handler_t *handler, dif_alert_handler_class_t alert_class,
    dif_alert_handler_toggle_t *state);

/**
 * Sets whether a particular interrupt is currently enabled or disabled.
 *
 * @param handler An alert handler handle.
 * @param alert_class An alert class.
 * @param state The new toggle state for the interrupt.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_alert_handler_result_t dif_alert_handler_irq_set_enabled(
    const dif_alert_handler_t *handler, dif_alert_handler_class_t alert_class,
    dif_alert_handler_toggle_t state);

/**
 * Forces a particular interrupt, causing it to be serviced as if hardware had
 * asserted it.
 *
 * @param handler An alert handler handle.
 * @param alert_class An alert class.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_alert_handler_result_t dif_alert_handler_irq_force(
    const dif_alert_handler_t *handler, dif_alert_handler_class_t alert_class);

/**
 * Disables all interrupts, optionally snapshotting all toggle state for later
 * restoration.
 *
 * @param handler An alert handler handle.
 * @param snapshot Out-param for the snapshot; may be `NULL`.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_alert_handler_result_t dif_alert_handler_irq_disable_all(
    const dif_alert_handler_t *handler,
    dif_alert_handler_irq_snapshot_t *snapshot);

/**
 * Restores interrupts from the given snapshot.
 *
 * This function can be used with `dif_alert_handler_irq_disable_all()` to
 * temporary
 * interrupt save-and-restore.
 *
 * @param handler An alert handler handle.
 * @param snapshot A snapshot to restore from.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_alert_handler_result_t dif_alert_handler_irq_restore_all(
    const dif_alert_handler_t *handler,
    const dif_alert_handler_irq_snapshot_t *snapshot);

/**
 * Checks whether an alert is one of the causes for an alert IRQ.
 *
 * Note that multiple alerts may be causes at the same time.
 *
 * @param handler An alert handler handle.
 * @param alert The alert to check.
 * @param is_cause Out-param for whether this alert is a cause.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_alert_handler_result_t dif_alert_handler_alert_is_cause(
    const dif_alert_handler_t *handler, dif_alert_handler_alert_t alert,
    bool *is_cause);

/**
 * Clears an alert from the cause vector, similar to an IRQ acknowledgement.
 *
 * @param handler An alert handler handle.
 * @param alert The alert to acknowledge.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_alert_handler_result_t dif_alert_handler_alert_acknowledge(
    const dif_alert_handler_t *handler, dif_alert_handler_alert_t alert);

/**
 * Checks whether a local alert is one of the causes for an alert IRQ.
 *
 * Note that multiple alerts may be causes at the same time.
 *
 * @param handler An alert handler handle.
 * @param alert The alert to check.
 * @param is_cause Out-param for whether this alert is a cause.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_alert_handler_result_t dif_alert_handler_local_alert_is_cause(
    const dif_alert_handler_t *handler, dif_alert_handler_local_alert_t alert,
    bool *is_cause);

/**
 * Clears a local alert from the cause vector, similar to an IRQ
 * acknowledgement.
 *
 * @param handler An alert handler handle.
 * @param alert The alert to acknowledge.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_alert_handler_result_t dif_alert_handler_local_alert_acknowledge(
    const dif_alert_handler_t *handler, dif_alert_handler_local_alert_t alert);

/**
 * Checks whether software can clear escalations for this class.
 *
 * If `automatic_locking` has been set in a class's configuration, this
 * function may suddenly begin returning `false` instead of `true` without
 * software invervention, if escalation has been triggered.
 *
 * @param handler An alert handler handle.
 * @param alert_class The class to check.
 * @param can_clear Out-param for the clear enablement state.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_alert_handler_result_t dif_alert_handler_escalation_can_clear(
    const dif_alert_handler_t *handler, dif_alert_handler_class_t alert_class,
    bool *can_clear);

/**
 * Disables escalation clearing for this class.
 *
 * This operation is similar to locking in that it cannot be undone.
 *
 * @param handler An alert handler handle.
 * @param alert_class The class to disable clearing for.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_alert_handler_result_t dif_alert_handler_escalation_disable_clearing(
    const dif_alert_handler_t *handler, dif_alert_handler_class_t alert_class);

/**
 * Clears an on-going escalation, as well as the class accumulator.
 *
 * This operation can be disabled with
 * `dif_alert_handler_escalation_disable_clearing()`.
 *
 * @param handler An alert handler handle.
 * @param alert_class The class to clear an escalation for.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_alert_handler_result_t dif_alert_handler_escalation_clear(
    const dif_alert_handler_t *handler, dif_alert_handler_class_t alert_class);

/**
 * Gets the accumulator value for this class.
 *
 * This value is the number of alerts of this class that have been logged so
 * far (more or less, since multiple alerts on the same cycle will be merged
 * into one). Once this value equals the configured threshold, any followup
 * alerts will immediately trigger the escalation protocol.
 *
 * This value is cleared as a side-effect of
 * `dif_alert_handler_escalation_clear()`.
 *
 * @param handler An alert handler handle.
 * @param alert_class The class to get the accumulator for.
 * @param alerts Out-param for the accumulator.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_alert_handler_result_t dif_alert_handler_get_accumulator(
    const dif_alert_handler_t *handler, dif_alert_handler_class_t alert_class,
    uint16_t *alerts);

/**
 * Gets the current value of the "escalation counter".
 *
 * The interpretation of this value depends on the value returned by
 * `dif_alert_handler_class_state_get()`. If it is in the timeout state,
 * it returns the number of cycles counted towards that cycle so far.
 * If in an escalation phase, it returns the number of cycles that phase
 * has been active for.
 *
 * @param handler An alert handler handle.
 * @param alert_class The class to set the counter for.
 * @param cycles Out-param for the counter.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_alert_handler_result_t dif_alert_handler_get_escalation_counter(
    const dif_alert_handler_t *handler, dif_alert_handler_class_t alert_class,
    uint32_t *cycles);

/**
 * Gets the current state of this class.
 *
 * See `dif_alert_handler_class_state_t` for potential states.
 *
 * @param handler An alert handler handle.
 * @param alert_class The class to get the state of
 * @param state Out-param for the class state.
 * @return The result of the operation.
 */
DIF_WARN_UNUSED_RESULT
dif_alert_handler_result_t dif_alert_handler_get_class_state(
    const dif_alert_handler_t *handler, dif_alert_handler_class_t alert_class,
    dif_alert_handler_class_state_t *state);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_ALERT_HANDLER_H_
