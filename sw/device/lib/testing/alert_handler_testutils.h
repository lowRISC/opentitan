// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_ALERT_HANDLER_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_ALERT_HANDLER_TESTUTILS_H_

#include <stdbool.h>

#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_rstmgr.h"

#include "alert_handler_regs.h"

typedef enum alert_handler_class_state {
  kCstateIdle = 0,
  kCstateTimeout = 1,
  kCstateTerminal = 3,
  kCstatePhase0 = 4,
  kCstatePhase1 = 5,
  kCstatePhase2 = 6,
  kCstatePhase3 = 7,
  kCstateFsmError = 2
} alert_handler_class_state_t;

/**
 * Represents the hardware alert crash dump in a more software-friendly manner.
 */
typedef struct alert_info {
  bool alert_cause[ALERT_HANDLER_PARAM_N_ALERTS];
  uint8_t loc_alert_cause;                                  // 7bit
  uint16_t class_accum_cnt[ALERT_HANDLER_PARAM_N_CLASSES];  // 4x16bit
  uint32_t class_esc_cnt[ALERT_HANDLER_PARAM_N_CLASSES];    // 4x32bit
  alert_handler_class_state_t
      class_esc_state[ALERT_HANDLER_PARAM_N_CLASSES];  // 4x3bit
} alert_info_t;

/**
 * Converts the hardware alert crash dump into an alert_info_t.
 *
 * This makes it easier to compare and display the different fields.
 */
alert_info_t alert_info_dump_to_struct(
    const dif_rstmgr_alert_info_dump_segment_t *dump, int dump_size);

/**
 * Displays an alert_info_t as strings.
 */
void alert_info_to_string(const alert_info_t *info);

/**
 * Configures alert handler with all required runtime information.
 *
 * This operation is lock-protected, meaning once the configuration is locked,
 * it cannot be reconfigured until after a system reset. If `locked` is set to
 * `kDifToggleEnabled`, then every lockable configuration will be locked.
 * Otherwise, configurations may only be locked by performing subsequent calls
 * to each component-specific locking DIF: `dif_alert_handler_lock_*(...)`.
 *
 * @param alert_handler An alert handler handle.
 * @param config Runtime configuration parameters.
 * @param locked The locked state to set for each configuration.
 */
void alert_handler_testutils_configure_all(
    const dif_alert_handler_t *alert_handler, dif_alert_handler_config_t config,
    dif_toggle_t locked);

/**
 * Returns the number of cycles corresponding to the given microseconds.
 */
uint32_t alert_handler_testutils_get_cycles_from_us(uint64_t microseconds);

/**
 * Returns a scaling factor for conversion of time to cycles.
 *
 * Setting escalation cycle counts must be such that the ISRs have time to
 * complete before the next escalation stage starts. We tend to generate cycle
 * counts from time durations, and given that the relevant clock frequencies
 * are much lower in non-sim_dv devices we may end up having to set quite high
 * time durations to avoid incomplete ISRs for fpga or verilator.
 *
 * This function allows the time durations to be set for the sim_dv clock
 * frequencies, and other platforms get the cycle count rescaled by a factor
 * of 10. It should be used in the conversion of time duration to cycle counts,
 * as in
 *  cycles = udiv64_slow(micros * clockFreqHz, 1000000, NULL) *
 *           cycle_rescaling_factor();
 */
uint32_t alert_handler_testutils_cycle_rescaling_factor();

/**
 * Returns whether an alert is active.
 *
 * @param alert_handler An alert handler handle.
 * @param alert The given alert.
 * @return The status of the given alert as boolean.
 */
bool alert_handler_testutils_is_alert_active(
    const dif_alert_handler_t *alert_handler, dif_alert_handler_alert_t alert);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_ALERT_HANDLER_TESTUTILS_H_
