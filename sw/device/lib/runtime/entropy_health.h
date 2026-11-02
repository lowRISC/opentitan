// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_RUNTIME_ENTROPY_HEALTH_H_
#define OPENTITAN_SW_DEVICE_LIB_RUNTIME_ENTROPY_HEALTH_H_

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * @file
 * @brief Software-Side Entropy Health Monitor
 *
 * This module provides defense-in-depth entropy health monitoring to satisfy
 * NIST SP 800-90B requirements (e.g., Repetition Count Test) against silent
 * hardware logic failures or bus faults.
 */

/**
 * The threshold for the Repetition Count Test (RCT).
 * If a symbol repeats this many times consecutively, the test fails.
 */
#define ENTROPY_HEALTH_RCT_THRESHOLD 31

/**
 * State for the Repetition Count Test (RCT).
 */
typedef struct entropy_health_rct_state {
  uint32_t current_symbol;
  uint32_t rep_count;
  uint32_t fail_flag; // 0 = OK, non-zero = Failed
} entropy_health_rct_state_t;

/**
 * Initializes the Repetition Count Test state.
 *
 * @param state A pointer to the RCT state to initialize.
 * @param first_symbol The very first symbol drawn from the entropy source.
 */
void entropy_health_rct_init(entropy_health_rct_state_t *state,
                             uint32_t first_symbol);

/**
 * Updates the RCT state with a new symbol using branchless logic.
 *
 * @param state A pointer to the RCT state.
 * @param new_symbol The newly drawn symbol from the entropy source.
 */
void entropy_health_rct_update(entropy_health_rct_state_t *state,
                               uint32_t new_symbol);

/**
 * Checks if the RCT has failed.
 *
 * Once this function returns true, it will continue to return true for the
 * lifetime of the state object (until re-initialized).
 *
 * @param state A pointer to the RCT state.
 * @return True if a failure has occurred, false otherwise.
 */
OT_WARN_UNUSED_RESULT
bool entropy_health_rct_has_failed(const entropy_health_rct_state_t *state);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_RUNTIME_ENTROPY_HEALTH_H_
