// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_TESTS_PWRMGR_SLEEP_RESETS_LIB_H_
#define OPENTITAN_SW_DEVICE_TESTS_PWRMGR_SLEEP_RESETS_LIB_H_

#include <stdint.h>

#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"

/**
 * Some shared times in microsconds.
 *
 * Program the alert handler to escalate on alerts upto phase 2 (i.e. reset) but
 * the phase 1 (i.e. wipe secrets) should occur and last during the time the
 * wdog is programed to bark.
 *
 * Notice these settings are suitable for sim_dv. For some other platforms
 * they are uniformly rescaled.
 */
typedef enum pwmgr_sleep_resets_lib_times {
  kWdogBarkMicros = 3 * 100,          // 300 us
  kWdogBiteMicros = 4 * 100,          // 400 us
  kEscalationPhase0Micros = 1 * 100,  // 100 us
  // The cpu value is slightly larger to avoid flakey results.
  kEscalationPhase0MicrosCpu = kEscalationPhase0Micros + 20,  // 120 us
  kEscalationPhase1Micros = 5 * 100,                          // 500 us
  kEscalationPhase2Micros = 50,                               // 50 us
  // Allow a long wait before the reset is received, since the host needs
  // to read and parse the log message before it changes the pin values.
  kWaitWhileActiveMicros = 80000,  // 80 ms
} pwmgr_sleep_resets_lib_times_t;

/**
 * The modes of the tests using this library.
 */
typedef enum pwrmgr_sleep_resets_lib_modes {
  /**
   * Deep sleep mode.
   */
  kPwrmgrSleepResetsLibModesDeepSleep = 1,

  /**
   * Normal sleep mode.
   */
  kPwrmgrSleepResetsLibModesNormalSleep = 2,

  /**
   * Active mode (no sleep).
   */
  kPwrmgrSleepResetsLibModesActive = 3
} pwrmgr_sleep_resets_lib_modes_t;

/**
 * Objects to access the peripherals used in this test via dif API.
 */
extern dif_flash_ctrl_state_t *flash_ctrl;
extern dif_rv_plic_t *plic;
extern dif_rstmgr_t *rstmgr;

/**
 * Initialize the peripherals used in this test.
 */
void init_peripherals(void);

/**
 * Program the alert handler to escalate on alerts upto phase 2 (i.e. reset) but
 * the phase 1 (i.e. wipe secrets) should occur and last during the time the
 * wdog is programed to bark.
 */
void config_alert_handler(void);

/**
 * Configure the sysrst to trigger a reset with a combo triggered by key0,
 * and enable it as a reset source. The pinmux configures pad_pin to connect
 * to key0.
 */
void config_sysrst(dif_pinmux_index_t pad_pin);

/**
 * Configure the wdog cycle counts and enable it as a reset source.
 * Enabling it as reset source needs a domain crossing to the aon domain,
 * so it consumes up to 10 us.
 */
void config_wdog(uint64_t bark_micros, uint64_t bite_micros);

/**
 * Trigger escalation together with a watchdog.
 *
 * The watchdog is expected to have no effect when escalation is triggered.
 */
void trigger_escalation(void);

/**
 * Prepare for watchdog reset.
 *
 * Enable watchdog reset, and spin wait or enter either normal or deep sleep.
 */
void prepare_for_wdog(pwrmgr_sleep_resets_lib_modes_t mode);

/**
 * Prepare for sysrst reset.
 *
 * Enable sysrst reset, and spin wait or enter either normal or deep sleep .
 */
void prepare_for_sysrst(pwrmgr_sleep_resets_lib_modes_t mode);

/**
 * External ISR.
 *
 * Handles all peripheral interrupts expected for these tests. It expects
 * no barks from aon_timer, and phase 0 interrupts from the alert handler.
 */
void ottf_external_isr(void);

#endif  // OPENTITAN_SW_DEVICE_TESTS_PWRMGR_SLEEP_RESETS_LIB_H_
