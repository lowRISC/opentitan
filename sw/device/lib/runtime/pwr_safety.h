// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_RUNTIME_PWR_SAFETY_H_
#define OPENTITAN_SW_DEVICE_LIB_RUNTIME_PWR_SAFETY_H_

/**
 * @file
 * @brief Power-Safety Sleep-Entry Validation Utility
 *
 * ## Background
 *
 * OpenTitan's Alert Handler is the primary hardware defence-in-depth
 * mechanism against hardware tampering and fault-injection attacks.  When
 * any of the four alert classes (A, B, C, D) transitions out of the Idle
 * state, an escalation protocol begins that may ultimately scrub the life-
 * cycle state or issue a full chip reset.
 *
 * The RISC-V `wfi` (Wait For Interrupt) instruction puts the Ibex core into
 * a power-gated state.  If the power manager's `LOW_POWER_HINT` bit is set at
 * the time of `wfi`, the hardware transitions to low-power mode.  A critical
 * gap exists between:
 *   1. Software enabling low-power mode via
 *      `dif_pwrmgr_low_power_set_enabled(..., kDifToggleEnabled, ...)`, and
 *   2. The subsequent `wfi` instruction that actually enters sleep.
 *
 * If an Alert Handler escalation protocol is already in progress at this
 * moment, the CPU will stop executing while the escalation counter continues
 * to tick.  Depending on the configured phase durations, the hardware
 * countermeasure (e.g., LC-state scrapping via escalation signal 1/2) may
 * fire *during* the low-power period — before the CPU is awake to service
 * the interrupt.  This undermines the Root of Trust's security posture.
 *
 * ## This Utility
 *
 * `pwr_safety_check_sleep_readiness()` gates sleep entry by:
 *
 *   1. Querying the Alert Handler's class-state FSM for all four classes
 *      (A, B, C, D).  Any state other than `kDifAlertHandlerClassStateIdle`
 *      is considered "unsafe" — it indicates that an alert has been received
 *      and the escalation protocol has started, timed out, or entered a
 *      terminal/FSM-error condition.
 *
 *   2. Querying the power manager's fault-status register for any latched
 *      fatal errors (register-file integrity, escalation timeout, or main-
 *      power glitch).  Any latched error indicates the power domain is
 *      already compromised.
 *
 * If either check fails the function returns `false`, and the caller MUST NOT
 * arm `wfi` in low-power mode.  The caller should instead service the pending
 * alert class via its IRQ handler, and clear the escalation before retrying.
 *
 * ## Usage Contract
 *
 * ```c
 * if (!pwr_safety_check_sleep_readiness(&alert_handler, &pwrmgr)) {
 *   // Do NOT enter low-power sleep; service pending alert first.
 *   return;
 * }
 * CHECK_DIF_OK(dif_pwrmgr_low_power_set_enabled(
 *     &pwrmgr, kDifToggleEnabled, kDifToggleEnabled));
 * wait_for_interrupt();   // wfi
 * ```
 *
 * ## C11 Freestanding Compliance
 *
 * This file includes only freestanding headers (`<stdbool.h>`, `<stdint.h>`).
 * All DIF headers transitively include only freestanding-compatible headers on
 * device builds.
 */

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Result codes for `pwr_safety_check_sleep_readiness`.
 *
 * A dedicated enum is used (rather than a raw `bool`) so that call-sites can
 * distinguish DIF communication errors from a genuine "unsafe" verdict.
 */
typedef enum pwr_safety_sleep_result {
  /**
   * All alert classes are idle and no fatal power errors are latched.
   * It is safe to arm the power manager and execute `wfi`.
   */
  kPwrSafetySleepResultSafe = 0,

  /**
   * At least one alert class is in a non-idle state (Timeout, Phase0–3,
   * Terminal, or FsmError).  Sleep entry must be deferred until the alert
   * has been serviced and the escalation cleared.
   */
  kPwrSafetySleepResultAlertPending = 1,

  /**
   * A fatal power-manager error is latched (regfile integrity, escalation
   * timeout, or main-power glitch).  Sleep entry is not permitted; the
   * system should initiate a secure shutdown.
   */
  kPwrSafetySleepResultFatalPowerError = 2,

  /**
   * A DIF call returned an unexpected error while reading hardware state.
   * The caller should treat this as "unsafe" and must not enter sleep.
   */
  kPwrSafetySleepResultDifError = 3,
} pwr_safety_sleep_result_t;

/**
 * Check whether it is safe to enter low-power sleep.
 *
 * This function interrogates the Alert Handler's per-class FSM state for
 * all four classes (A, B, C, D) and the power manager's fault-status
 * register.  It returns a `pwr_safety_sleep_result_t` describing the
 * outcome.
 *
 * The function is intentionally *non-modifying*: it does not clear any
 * alert, acknowledge any interrupt, or write to the power manager.  All
 * hardware-state changes remain the responsibility of the caller (e.g., the
 * alert IRQ handler or the shutdown sequence).
 *
 * @param alert_handler  Initialised handle to the Alert Handler peripheral.
 * @param pwrmgr         Initialised handle to the Power Manager peripheral.
 * @return               `kPwrSafetySleepResultSafe` iff sleep is permitted.
 *                       Any other value means sleep MUST NOT be entered.
 */
OT_WARN_UNUSED_RESULT
pwr_safety_sleep_result_t pwr_safety_check_sleep_readiness(
    const dif_alert_handler_t *alert_handler, const dif_pwrmgr_t *pwrmgr);

/**
 * Convenience wrapper: returns `true` iff sleep is safe.
 *
 * This thin wrapper discards the reason code.  Prefer the full-result variant
 * when the caller needs to take class-specific recovery actions.
 *
 * @param alert_handler  Initialised handle to the Alert Handler peripheral.
 * @param pwrmgr         Initialised handle to the Power Manager peripheral.
 * @return               `true` iff `kPwrSafetySleepResultSafe`.
 */
OT_WARN_UNUSED_RESULT
static inline bool pwr_safety_is_sleep_safe(
    const dif_alert_handler_t *alert_handler, const dif_pwrmgr_t *pwrmgr) {
  return pwr_safety_check_sleep_readiness(alert_handler, pwrmgr) ==
         kPwrSafetySleepResultSafe;
}

// Extern declaration for the `static inline` above; provides a link location
// in translation units that do not inline the wrapper.
extern bool pwr_safety_is_sleep_safe(const dif_alert_handler_t *,
                                     const dif_pwrmgr_t *);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_RUNTIME_PWR_SAFETY_H_
