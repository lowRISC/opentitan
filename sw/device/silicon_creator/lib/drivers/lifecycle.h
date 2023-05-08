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
 * Lifecycle states.
 *
 * This is a condensed version of the 24 possible life cycle states where
 * TEST_UNLOCKED_* states are mapped to `kLcStateTest` and invalid states where
 * CPU execution is disabled are omitted.
 *
 * Encoding generated with
 * $ ./util/design/sparse-fsm-encode.py -d 6 -m 5 -n 32 \
 *     -s 2447090565 --language=c
 *
 * Minimum Hamming distance: 13
 * Maximum Hamming distance: 19
 * Minimum Hamming weight: 15
 * Maximum Hamming weight: 20
 */
typedef enum lifecycle_state {
  /**
   * Unlocked test state where debug functions are enabled.
   *
   * Corresponds to TEST_UNLOCKED_* life cycle states.
   */
  kLcStateTest = 0xb2865fbb,
  /**
   * Development life cycle state where limited debug functionality is
   * available.
   */
  kLcStateDev = 0x0b5a75e0,
  /**
   * Production life cycle state.
   */
  kLcStateProd = 0x65f2520f,
  /**
   * Same as PROD, but transition into RMA is not possible from this state.
   */
  kLcStateProdEnd = 0x91b9b68a,
  /**
   * RMA life cycle state.
   */
  kLcStateRma = 0xcf8cfaab,
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
 * Hardware revision.
 *
 * Consists of a 16-bit silicon creator ID,
 * a 16-bit product ID and an 8bit revision ID.
 */
typedef struct lifecycle_hw_rev {
  uint16_t silicon_creator_id;
  uint16_t product_id;
  uint8_t revision_id;
} lifecycle_hw_rev_t;

/**
 * Get the life cycle state.
 *
 * This function checks the value read from the hardware and returns a
 * `life_cycle_state_t`. See `life_cyle_state_t` for more details.
 *
 * @return Life cycle state.
 */
lifecycle_state_t lifecycle_state_get(void);

/**
 * Get the unprocessed life cycle state value read from the hardware.
 *
 * This function directly returns the `uint32_t` value read from the hardware.
 *
 * @return Life cycle state.
 */
uint32_t lifecycle_raw_state_get(void);

/**
 * Get the device identifier.
 *
 * @param[out] device_id 256-bit device identifier that is stored in the
 * `HW_CFG` partition in OTP.
 */
void lifecycle_device_id_get(lifecycle_device_id_t *device_id);

/**
 * Get the hardware revision.
 *
 * @param[out] hw_rev Hardware revision.
 */
void lifecycle_hw_rev_get(lifecycle_hw_rev_t *hw_rev);

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_LIFECYCLE_H_
