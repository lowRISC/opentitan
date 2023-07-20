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

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "sw/device/lib/dif/autogen/dif_alert_handler_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Helper X macro for defining enums and case statements related to alert
 * classes. If an additional class is ever added to the hardware, this list can
 * be updated.
 */
#define LIST_OF_CLASSES(X) \
  X(A, 0)                  \
  X(B, 1)                  \
  X(C, 2)                  \
  X(D, 3)

/**
 * Helper macro for defining a `dif_alert_handler_class_t` enumeration constant.
 * @class_ Alert class of the enumeration constant.
 * @value_ Value of the enumeration constant.
 */
#define ALERT_CLASS_ENUM_INIT_(class_, value_) \
  kDifAlertHandlerClass##class_ = value_,

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
  LIST_OF_CLASSES(ALERT_CLASS_ENUM_INIT_)
} dif_alert_handler_class_t;

/**
 * An alert, identified by a numeric id.
 *
 * Alerts are hardware-level events indicating that something catastrophic
 * has happened. The alert handler consumes alerts, classifies them into a
 * particular `dif_alert_handler_class_t`, and uses policy information attached
 * to that class to handle it.
 *
 * The number of alerts is configurable at hardware-synthesis time.
 */
typedef uint32_t dif_alert_handler_alert_t;

/**
 * Helper X macro for defining enums and case statements related to local
 * alerts. If an additional class is ever added to the hardware, this list can
 * be updated.
 */
#define LIST_OF_LOC_ALERTS(X)                             \
  X(kDifAlertHandlerLocalAlertAlertPingFail, 0)           \
  X(kDifAlertHandlerLocalAlertEscalationPingFail, 1)      \
  X(kDifAlertHandlerLocalAlertAlertIntegrityFail, 2)      \
  X(kDifAlertHandlerLocalAlertEscalationIntegrityFail, 3) \
  X(kDifAlertHandlerLocalAlertBusIntegrityFail, 4)        \
  X(kDifAlertHandlerLocalAlertShadowedUpdateError, 5)     \
  X(kDifAlertHandlerLocalAlertShadowedStorageError, 6)

/**
 * Helper macro for defining a `dif_alert_handler_local_alert_t` enumeration
 * constant.
 * @name_ Name of the enumeration constant.
 */
#define LOC_ALERT_ENUM_INIT_(name_, value_) name_ = value_,

/**
 * A local alert originating from within the alert handler itself.
 *
 * A local alert is exactly the same as a normal `dif_alert_handler_alert_t`,
 * except that they use different functions for setting up classification and
 * for getting causes.
 */
typedef enum dif_alert_handler_local_alert {
  LIST_OF_LOC_ALERTS(LOC_ALERT_ENUM_INIT_)
} dif_alert_handler_local_alert_t;

/**
 * An alert class state.
 *
 * This enum describes the sequence of states in the *escalation protocol*,
 * which triggers under two different conditions:
 * - If too many alerts of a particular class accumulate.
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
 * the state back to idle. Note that this function cannot clear the terminal
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
 * An escalation signal, identified by a numeric ID.
 *
 * An escalation signal is a generic "response" to failing to handle alert(s).
 * The meaning of each escalation signal is determined by the chip.
 *
 * An alert class can be configured to raise various escalation signal(s) during
 * various escalation phases as part of its escalation policy.
 */
typedef uint32_t dif_alert_handler_escalation_signal_t;

/**
 * Runtime configuration for an escalation phase.
 */
typedef struct dif_alert_handler_escalation_phase {
  /**
   * The phase this configuration describes.
   *
   * It is an error for this to not be one of the `Phase` constants in
   * `dif_alert_handler_class_state_t`.
   */
  dif_alert_handler_class_state_t phase;
  /**
   * The escalation signal that should be triggered when this phase begins.
   */
  dif_alert_handler_escalation_signal_t signal;
  /**
   * The duration of this phase, in cycles.
   */
  uint32_t duration_cycles;
} dif_alert_handler_escalation_phase_t;

/**
 * Runtime configuration for a particular alert class.
 *
 * This struct describes the escalation protocol for an alert class.
 */
typedef struct dif_alert_handler_class_config {
  /**
   * Whether to automatically lock the accumulation counter.
   *
   * There are two ways to lock the accumulation counter (prevent it from being
   * cleared once the class's escalation protocol has been triggered):
   *   1. clear the write enable for the accumulation counter clear register, or
   *   2. to set this configuration flag which will automatically clear the
   *      write enable for the accumulation counter clear register once the
   *      class's escalation protocol has been triggered.
   */
  dif_toggle_t auto_lock_accumulation_counter;
  /**
   * The threshold for the class accmulator which indicates the number of alerts
   * that must fire because the class's escalation protocol will trigger.
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
   * Escalation phases to be configured for this class.
   *
   * Each escalation phase in this list will additionally be set as enabled for
   * this class; phases not listed will have their escalation signals disabled.
   */
  const dif_alert_handler_escalation_phase_t *escalation_phases;
  /**
   * The length of the array `escalation_phases`.
   */
  size_t escalation_phases_len;
  /**
   * The escalation phase to capture the crashdump information in.
   *
   * It is an error for this to not be one of the `Phase` constants in
   * `dif_alert_handler_class_state_t`.
   *
   * Note, it is recommended to capture the crashdump upon entering the first
   * escalation phase that activates a countermeasure with many side-effects
   * (e.g. life cycle state scrapping) in order to prevent spurious alert events
   * from masking the original alert causes.
   */
  dif_alert_handler_class_state_t crashdump_escalation_phase;
} dif_alert_handler_class_config_t;

/**
 * Runtime configuration for the alert handler.
 *
 * This struct describes runtime information for a single-shot configuration of
 * the alert handler hardware.
 *
 * Note, any of the array pointers may be NULL, in which case the associated
 * length should be 0.
 */
typedef struct dif_alert_handler_config {
  /**
   * A list of alerts to configure.
   */
  dif_alert_handler_alert_t *alerts;
  /**
   * A list of classes to assign each alert to.
   */
  dif_alert_handler_class_t *alert_classes;
  /**
   * The lengths of the arrays `alerts` and `alert_classes`.
   */
  size_t alerts_len;

  /**
   * A list of local alerts to configure.
   */
  dif_alert_handler_local_alert_t *local_alerts;
  /**
   * A list of classes to assign each local alert to.
   */
  dif_alert_handler_class_t *local_alert_classes;
  /**
   * The lengths of the arrays `local_alerts` and `local_alert_classes`.
   */
  size_t local_alerts_len;

  /**
   * A list of alert classes to configure.
   */
  const dif_alert_handler_class_t *classes;
  /**
   * A list of alert class (escalation protocol) configurations.
   */
  const dif_alert_handler_class_config_t *class_configs;
  /**
   * The length of the arrays `classes` and `class_configs`.
   */
  size_t classes_len;

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
   * Note while this value must fit into the timeout register which is smaller
   * than the native word length.
   */
  uint32_t ping_timeout;

} dif_alert_handler_config_t;

/**
 * Configures an alert in the alert handler.
 *
 * This operation is lock-protected, meaning once the configuration is locked,
 * it cannot be reconfigured until after a system reset.
 *
 * @param alert_handler An alert handler handle.
 * @param alert The alert to be configured.
 * @param alert_class The class to assign the alert to.
 * @param enabled The enablement state to configure the alert in.
 * @param locked The locked state to configure the alert in.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_configure_alert(
    const dif_alert_handler_t *alert_handler, dif_alert_handler_alert_t alert,
    dif_alert_handler_class_t alert_class, dif_toggle_t enabled,
    dif_toggle_t locked);

/**
 * Configures a local alert in the alert handler.
 *
 * This operation is lock-protected, meaning once the configuration is locked,
 * it cannot be reconfigured until after a system reset.
 *
 * @param alert_handler An alert handler handle.
 * @param local_alert The local alert to be configured.
 * @param alert_class The class to assign the alert to.
 * @param enabled The enablement state to configure the alert in.
 * @param locked The locked state to configure the alert in.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_configure_local_alert(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_local_alert_t local_alert,
    dif_alert_handler_class_t alert_class, dif_toggle_t enabled,
    dif_toggle_t locked);

/**
 * Configures the escalation protocol of an alert class in the alert handler.
 *
 * This operation is lock-protected, meaning once the configuration is locked,
 * it cannot be reconfigured until after a system reset.
 *
 * Note, regardless if the class is enabled or, IRQs will still fire based on
 * the accumulation counter threshold configuration for the class, however, the
 * escalation protocol will not trigger.
 *
 * @param alert_handler An alert handler handle.
 * @param alert_class The class to be configured.
 * @param config The escalation protocol configuration.
 * @param enabled The enablement state of the class escalation protocol.
 * @param locked The locked state to configure the class in.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_configure_class(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_class_t alert_class,
    dif_alert_handler_class_config_t config, dif_toggle_t enabled,
    dif_toggle_t locked);

/**
 * Configures the ping timer in the alert handler.
 *
 * This operation is lock-protected, meaning once the configuration is locked,
 * it cannot be reconfigured until after a system reset.
 *
 * Note, the ping timer will only ping alerts that have been enabled AND locked.
 * Therefore, this DIF should be invoked after configuring and enabling each
 * (local) alert.
 *
 * @param alert_handler An alert handler handle.
 * @param ping_timeout The alert ping timeout, in cycles.
 * @param enabled The enablement state to configure the ping timer in.
 * @param locked The locked state to configure ping timer in.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_configure_ping_timer(
    const dif_alert_handler_t *alert_handler, uint32_t ping_timeout,
    dif_toggle_t enabled, dif_toggle_t locked);

/**
 * Enables the ping timer in the alert handler.
 *
 * This operation is lock-protected, meaning once the configuration is locked,
 * it cannot be reconfigured until after a system reset.
 *
 * Note, the ping timer will only ping alerts that have been enabled AND locked.
 * Therefore, this DIF should be invoked after configuring and enabling each
 * (local) alert.
 *
 * @param alert_handler An alert handler handle.
 * @param locked The locked state to configure ping timer in after enabling it.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_ping_timer_set_enabled(
    const dif_alert_handler_t *alert_handler, dif_toggle_t locked);

/**
 * Locks out an alert handler alert configuration.
 *
 * This operation cannot be undone, and should be performed at the end of
 * configuring the alert handler in early boot.
 *
 * This function is reentrant: calling it while functionality is locked will
 * have no effect and return `kDifOk`.
 *
 * @param alert_handler An alert handler handle.
 * @param alert The alert to lock.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_lock_alert(
    const dif_alert_handler_t *alert_handler, dif_alert_handler_alert_t alert);

/**
 * Checks whether an alert handler's alert is locked.
 *
 * @param alert_handler An alert handler handle.
 * @param alert The alert to check is locked.
 * @param[out] is_locked Out-param for the locked state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_is_alert_locked(
    const dif_alert_handler_t *alert_handler, dif_alert_handler_alert_t alert,
    bool *is_locked);

/**
 * Locks out an alert handler local alert configuration.
 *
 * This operation cannot be undone, and should be performed at the end of
 * configuring the alert handler in early boot.
 *
 * This function is reentrant: calling it while functionality is locked will
 * have no effect and return `kDifOk`.
 *
 * @param alert_handler An alert handler handle.
 * @param local_alert The local alert to lock.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_lock_local_alert(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_local_alert_t local_alert);

/**
 * Checks whether an alert handler's local alert is locked.
 *
 * @param alert_handler An alert handler handle.
 * @param local_alert The local alert to check is locked.
 * @param[out] is_locked Out-param for the locked state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_is_local_alert_locked(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_local_alert_t local_alert, bool *is_locked);

/**
 * Locks out an alert handler class configuration.
 *
 * This operation cannot be undone, and should be performed at the end of
 * configuring the alert handler in early boot.
 *
 * This function is reentrant: calling it while functionality is locked will
 * have no effect and return `kDifOk`.
 *
 * @param alert_handler An alert handler handle.
 * @param alert_class The alert class to lock.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_lock_class(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_class_t alert_class);

/**
 * Checks whether an alert handler's class is locked.
 *
 * @param alert_handler An alert handler handle.
 * @param alert_class The alert class to check is locked.
 * @param[out] is_locked Out-param for the locked state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_is_class_locked(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_class_t alert_class, bool *is_locked);

/**
 * Locks out alert handler ping timer configuration.
 *
 * This operation cannot be undone, and should be performed at the end of
 * configuring the alert handler in early boot.
 *
 * This function is reentrant: calling it while functionality is locked will
 * have no effect and return `kDifOk`.
 *
 * @param alert_handler An alert handler handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_lock_ping_timer(
    const dif_alert_handler_t *alert_handler);

/**
 * Checks whether alert handler's ping timer is locked.
 *
 * @param alert_handler An alert handler handle.
 * @param[out] is_locked Out-param for the locked state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_is_ping_timer_locked(
    const dif_alert_handler_t *alert_handler, bool *is_locked);

/**
 * Checks whether an alert is one of the causes for an alert IRQ.
 *
 * Note that multiple alerts may be causes at the same time.
 *
 * @param alert_handler An alert handler handle.
 * @param alert The alert to check.
 * @param[out] is_cause Out-param for whether this alert is a cause.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_alert_is_cause(
    const dif_alert_handler_t *alert_handler, dif_alert_handler_alert_t alert,
    bool *is_cause);

/**
 * Clears an alert from the cause vector, similar to an IRQ acknowledgement.
 *
 * @param alert_handler An alert handler handle.
 * @param alert The alert to acknowledge.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_alert_acknowledge(
    const dif_alert_handler_t *alert_handler, dif_alert_handler_alert_t alert);

/**
 * Checks whether a local alert is one of the causes for an alert IRQ.
 *
 * Note that multiple alerts may be causes at the same time.
 *
 * @param alert_handler An alert handler handle.
 * @param local_alert The local alert to check.
 * @param[out] is_cause Out-param for whether this alert is a cause.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_local_alert_is_cause(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_local_alert_t local_alert, bool *is_cause);

/**
 * Clears a local alert from the cause vector, similar to an IRQ
 * acknowledgement.
 *
 * @param alert_handler An alert handler handle.
 * @param local_alert The local alert to acknowledge.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_local_alert_acknowledge(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_local_alert_t local_alert);

/**
 * Checks whether software can clear escalations for this class.
 *
 * If `automatic_locking` has been set in a class's configuration, this
 * function may suddenly begin returning `false` instead of `true` without
 * software invervention, if escalation has been triggered.
 *
 * @param alert_handler An alert handler handle.
 * @param alert_class The class to check.
 * @param[out] can_clear Out-param for the clear enablement state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_escalation_can_clear(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_class_t alert_class, bool *can_clear);

/**
 * Disables escalation clearing for this class.
 *
 * This operation is similar to locking in that it cannot be undone.
 *
 * @param alert_handler An alert handler handle.
 * @param alert_class The class to disable clearing for.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_escalation_disable_clearing(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_class_t alert_class);

/**
 * Clears an on-going escalation, as well as the class accumulator.
 *
 * This operation can be disabled with
 * `dif_alert_handler_escalation_disable_clearing()`.
 *
 * @param alert_handler An alert handler handle.
 * @param alert_class The class to clear an escalation for.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_escalation_clear(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_class_t alert_class);

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
 * @param alert_handler An alert handler handle.
 * @param alert_class The class to get the accumulator for.
 * @param[out] num_alerts Out-param for the number of alerts that have
 * accumulated.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_get_accumulator(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_class_t alert_class, uint16_t *num_alerts);

/**
 * Gets the current value of the "escalation counter".
 *
 * The interpretation of this value depends on the value returned by
 * `dif_alert_handler_class_state_get()`. If it is in the timeout state,
 * it returns the number of cycles counted towards that cycle so far.
 * If in an escalation phase, it returns the number of cycles that phase
 * has been active for.
 *
 * @param alert_handler An alert handler handle.
 * @param alert_class The class to set the counter for.
 * @param[out] cycles Out-param for the counter.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_get_escalation_counter(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_class_t alert_class, uint32_t *cycles);

/**
 * Gets the current state of this class.
 *
 * See `dif_alert_handler_class_state_t` for potential states.
 *
 * @param alert_handler An alert handler handle.
 * @param alert_class The class to get the state of
 * @param[out] state Out-param for the class state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_alert_handler_get_class_state(
    const dif_alert_handler_t *alert_handler,
    dif_alert_handler_class_t alert_class,
    dif_alert_handler_class_state_t *state);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_ALERT_HANDLER_H_
