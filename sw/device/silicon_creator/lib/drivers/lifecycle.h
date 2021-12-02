// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_LIFECYCLE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_LIFECYCLE_H_

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Lifecycle States.
 */
typedef enum LcState {
  /**
   * Raw life cycle state after fabrication where all functions are disabled.
   */
  kLcStateRaw = 0x0,
  /**
   * Unlocked test state where debug functions are enabled.
   */
  kLcStateTestUnlocked0 = 1 * 0x2108421,
  /**
   * Locked test state where where all functions are disabled.
   */
  kLcStateTestLocked0 = 2 * 0x2108421,
  /**
   * Unlocked test state where debug functions are enabled.
   */
  kLcStateTestUnlocked1 = 3 * 0x2108421,
  /**
   * Locked test state where where all functions are disabled.
   */
  kLcStateTestLocked1 = 4 * 0x2108421,
  /**
   * Unlocked test state where debug functions are enabled.
   */
  kLcStateTestUnlocked2 = 5 * 0x2108421,
  /**
   * Locked test state where debug all functions are disabled.
   */
  kLcStateTestLocked2 = 6 * 0x2108421,
  /**
   * Unlocked test state where debug functions are enabled.
   */
  kLcStateTestUnlocked3 = 7 * 0x2108421,
  /**
   * Locked test state where debug all functions are disabled.
   */
  kLcStateTestLocked3 = 8 * 0x2108421,
  /**
   * Unlocked test state where debug functions are enabled.
   */
  kLcStateTestUnlocked4 = 9 * 0x2108421,
  /**
   * Locked test state where debug all functions are disabled.
   */
  kLcStateTestLocked4 = 10 * 0x2108421,
  /**
   * Unlocked test state where debug functions are enabled.
   */
  kLcStateTestUnlocked5 = 11 * 0x2108421,
  /**
   * Locked test state where debug all functions are disabled.
   */
  kLcStateTestLocked5 = 12 * 0x2108421,
  /**
   * Unlocked test state where debug functions are enabled.
   */
  kLcStateTestUnlocked6 = 13 * 0x2108421,
  /**
   * Locked test state where debug all functions are disabled.
   */
  kLcStateTestLocked6 = 14 * 0x2108421,
  /**
   * Unlocked test state where debug functions are enabled.
   */
  kLcStateTestUnlocked7 = 15 * 0x2108421,
  /**
   * Development life cycle state where limited debug functionality is
   * available.
   */
  kLcStateDev = 16 * 0x2108421,
  /**
   * Production life cycle state.
   */
  kLcStateProd = 17 * 0x2108421,
  /**
   * Same as PROD, but transition into RMA is not possible from this state.
   */
  kLcStateProdEnd = 18 * 0x2108421,
  /**
   * RMA life cycle state.
   */
  kLcStateRma = 19 * 0x2108421,
  /**
   * SCRAP life cycle state where all functions are disabled.
   */
  kLcStateScrap = 20 * 0x2108421,
  /**
   * This state is temporary and behaves the same way as SCRAP.
   */
  kLcStatePostTransition = 21 * 0x2108421,
  /**
   * This state is temporary and behaves the same way as SCRAP.
   */
  kLcStateEscalate = 22 * 0x2108421,
  /**
   * This state is reported when the life cycle state encoding is invalid.
   * This state is temporary and behaves the same way as SCRAP.
   */
  kLcStateInvalid = 23 * 0x2108421,
  /**
   * This is not a state - it is the total number of states.
   */
  kLcStateNumStates = 24,
} lifecycle_state_t;

enum {
  /**
   * Size of the device identifier in words.
   */
  kLifecycleDeviceIdNumWords = 8,
};

/**
 * 256-bit device identifier that is stored in the `HW_CFG` partition in OTP.
 */
typedef struct lifecycle_device_id {
  uint32_t device_id[kLifecycleDeviceIdNumWords];
} lifecycle_device_id_t;

/**
 * Get the life cycle state.
 *
 * @return Life cycle state.
 */
lifecycle_state_t lifecycle_state_get(void);

/**
 * Get the human-readable name for a life cycle state.
 *
 * @param lc_state Life cycle state.
 * @return Name of the given state.
 */
const char *lifecycle_state_name_get(lifecycle_state_t lc_state);

/**
 * Get the device identifier.
 *
 * @param[out] device_id 256-bit device identifier that is stored in the
 * `HW_CFG` partition in OTP.
 */
void lifecycle_device_id_get(lifecycle_device_id_t *device_id);

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_LIFECYCLE_H_
