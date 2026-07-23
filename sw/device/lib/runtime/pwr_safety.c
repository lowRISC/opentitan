// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * @file
 * @brief Implementation of the power-safety sleep-entry validation utility.
 *
 * ## Security Rationale
 *
 * The OpenTitan Alert Handler implements a staged escalation protocol.  When
 * an alert fires, the relevant class FSM advances through:
 *
 *   Idle → Timeout → Phase0 → Phase1 → Phase2 → Phase3 → Terminal
 *
 * (or immediately to FsmError if the FSM itself is glitched).
 *
 * Each escalation phase may assert one or more escalation signals.  On the
 * Earl Grey top, escalation signals are wired to:
 *   - Signal 0: NMI to Ibex core.
 *   - Signal 1: Life-cycle state scrapping (irreversible).
 *   - Signal 2: Life-cycle state scrapping (redundant channel).
 *   - Signal 3: Full chip reset.
 *
 * If the CPU enters low-power sleep while a class is in the Timeout state,
 * the IRQ handler never runs, the escalation counter times out, and Phase0
 * begins — possibly asserting signal 0 (NMI) while Ibex is power-gated.  The
 * power manager's wakeup logic may not recognise an NMI from the alert handler
 * as a wakeup source, so the escalation continues advancing through the phases
 * until the chip resets or LC state is scrapped.
 *
 * This function closes the gap by performing a read-only audit of all four
 * class FSMs and the power manager's fault register before sleep is allowed.
 *
 * ## Implementation Notes
 *
 * - The checks are ordered: alert-class states first, power-fault second.
 *   This ensures the caller receives the most actionable result code (an
 *   alert state is recoverable; a fatal power fault is not).
 *
 * - The `LIST_OF_CLASSES` X-macro from dif_alert_handler.h enumerates A, B,
 *   C, D.  We iterate over them manually using an explicit array to avoid
 *   relying on the macro in implementation code (which would create a tight
 *   coupling to the header's internal helper macros).
 *
 * - `dif_pwrmgr_fatal_err_code_get_codes` reads `PWRMGR_FAULT_STATUS`.  Any
 *   non-zero value indicates a latched fatal error.  The power manager spec
 *   states these bits are sticky and cleared only by a power-on reset, so
 *   even a single set bit is cause for refusing sleep entry.
 */

#include "sw/device/lib/runtime/pwr_safety.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"

/**
 * The four alert classes, in declaration order.
 *
 * Using a static const array (rather than iterating 0..3) makes the intent
 * explicit and avoids casting integers to the enum type.
 */
static const dif_alert_handler_class_t kAlertClasses[4] = {
    kDifAlertHandlerClassA,
    kDifAlertHandlerClassB,
    kDifAlertHandlerClassC,
    kDifAlertHandlerClassD,
};

pwr_safety_sleep_result_t pwr_safety_check_sleep_readiness(
    const dif_alert_handler_t *alert_handler, const dif_pwrmgr_t *pwrmgr) {
  // -------------------------------------------------------------------------
  // Step 1: Query the class-state FSM for every alert class.
  //
  // A class is "safe" only when it is in the Idle state.  Every other state
  // (Timeout, Phase0–3, Terminal, FsmError) indicates that an alert has been
  // received and the escalation protocol is either pending, in flight, or has
  // already reached a terminal (bricked) state.
  //
  // Security requirement: this check MUST cover ALL four classes.  Checking
  // only "active" classes would allow an attacker to trigger an alert on an
  // ostensibly-disabled class to bypass the gate.  The hardware always tracks
  // the state of every class regardless of its software-enable bit, so
  // reading the state register is always meaningful.
  // -------------------------------------------------------------------------
  for (size_t i = 0; i < 4; ++i) {
    dif_alert_handler_class_state_t state;
    dif_result_t res =
        dif_alert_handler_get_class_state(alert_handler, kAlertClasses[i],
                                          &state);
    if (res != kDifOk) {
      // DIF communication failure — treat as unsafe.
      return kPwrSafetySleepResultDifError;
    }

    if (state != kDifAlertHandlerClassStateIdle) {
      // Any non-idle state: escalation is pending, in flight, or terminal.
      // The hardware has already raised (or is about to raise) an escalation
      // signal; sleep entry must be deferred.
      return kPwrSafetySleepResultAlertPending;
    }
  }

  // -------------------------------------------------------------------------
  // Step 2: Query the power manager's fault-status register.
  //
  // `PWRMGR_FAULT_STATUS` latches three classes of fatal error:
  //   - Bit 0 (REGFILE_INTEGRITY): A register-file ECC error was detected.
  //   - Bit 1 (ESC_TIMEOUT):       An escalation request from the alert
  //                                 handler was not acknowledged within the
  //                                 timeout window.
  //   - Bit 2 (MAIN_PD_GLITCH):    The main power domain experienced a glitch.
  //
  // All three are sticky: once set they remain set until the next power-on
  // reset.  Any non-zero value means the power subsystem is compromised and
  // the system should initiate a secure shutdown rather than sleeping.
  // -------------------------------------------------------------------------
  dif_pwrmgr_fatal_err_codes_t fault_codes;
  dif_result_t res =
      dif_pwrmgr_fatal_err_code_get_codes(pwrmgr, &fault_codes);
  if (res != kDifOk) {
    return kPwrSafetySleepResultDifError;
  }
  if (fault_codes != 0u) {
    return kPwrSafetySleepResultFatalPowerError;
  }

  // Both checks passed: all alert classes are idle and no power faults are
  // latched.  Sleep entry is permitted.
  return kPwrSafetySleepResultSafe;
}

// Provide the link-time definition of the `static inline` convenience wrapper
// declared in pwr_safety.h.  C11 §6.7.4p7.
extern bool pwr_safety_is_sleep_safe(const dif_alert_handler_t *alert_handler,
                                     const dif_pwrmgr_t *pwrmgr);
