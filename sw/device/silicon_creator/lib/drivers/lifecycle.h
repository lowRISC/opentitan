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
  kLcStateRaw,
  /**
   * Unlocked test state where debug functions are enabled.
   */
  kLcStateTestUnlocked0,
  /**
   * Locked test state where where all functions are disabled.
   */
  kLcStateTestLocked0,
  /**
   * Unlocked test state where debug functions are enabled.
   */
  kLcStateTestUnlocked1,
  /**
   * Locked test state where where all functions are disabled.
   */
  kLcStateTestLocked1,
  /**
   * Unlocked test state where debug functions are enabled.
   */
  kLcStateTestUnlocked2,
  /**
   * Locked test state where debug all functions are disabled.
   */
  kLcStateTestLocked2,
  /**
   * Unlocked test state where debug functions are enabled.
   */
  kLcStateTestUnlocked3,
  /**
   * Locked test state where debug all functions are disabled.
   */
  kLcStateTestLocked3,
  /**
   * Unlocked test state where debug functions are enabled.
   */
  kLcStateTestUnlocked4,
  /**
   * Locked test state where debug all functions are disabled.
   */
  kLcStateTestLocked4,
  /**
   * Unlocked test state where debug functions are enabled.
   */
  kLcStateTestUnlocked5,
  /**
   * Locked test state where debug all functions are disabled.
   */
  kLcStateTestLocked5,
  /**
   * Unlocked test state where debug functions are enabled.
   */
  kLcStateTestUnlocked6,
  /**
   * Locked test state where debug all functions are disabled.
   */
  kLcStateTestLocked6,
  /**
   * Unlocked test state where debug functions are enabled.
   */
  kLcStateTestUnlocked7,
  /**
   * Development life cycle state where limited debug functionality is
   * available.
   */
  kLcStateDev,
  /**
   * Production life cycle state.
   */
  kLcStateProd,
  /**
   * Same as PROD, but transition into RMA is not possible from this state.
   */
  kLcStateProdEnd,
  /**
   * RMA life cycle state.
   */
  kLcStateRma,
  /**
   * SCRAP life cycle state where all functions are disabled.
   */
  kLcStateScrap,
  /**
   * This state is temporary and behaves the same way as SCRAP.
   */
  kLcStatePostTransition,
  /**
   * This state is temporary and behaves the same way as SCRAP.
   */
  kLcStateEscalate,
  /**
   * This state is reported when the life cycle state encoding is invalid.
   * This state is temporary and behaves the same way as SCRAP.
   */
  kLcStateInvalid,
  /**
   * This is not a state - it is the total number of states.
   */
  kLcStateNumStates,
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

/*
 * An array of human-readable life cycle state names.
 */
extern const char *const lifecycle_state_name[];

/**
 * Get the life cycle state.
 *
 * @return Life cycle state.
 */
lifecycle_state_t lifecycle_state_get(void);

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
