// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_LIFECYCLE_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_LIFECYCLE_H_

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"

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
 * 256-bit device identifier that is stored in the `HW_CFG0` partition in OTP.
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
OT_WARN_UNUSED_RESULT
lifecycle_state_t lifecycle_state_get(void);

/**
 * Check if the device is in prod state.
 *
 * Warning: This function also returns false when LCS is invalid.
 *
 * @return `kHardenedBoolTrue` if the device is in prod state.
 */
OT_WARN_UNUSED_RESULT
hardened_bool_t lifecycle_is_prod(void);

/**
 * Get the unprocessed life cycle state value read from the hardware.
 *
 * This function directly returns the `uint32_t` value read from the hardware.
 *
 * @return Life cycle state.
 */
OT_WARN_UNUSED_RESULT
uint32_t lifecycle_raw_state_get(void);

/**
 * Get the device identifier.
 *
 * @param[out] device_id 256-bit device identifier that is stored in the
 * `HW_CFG0` partition in OTP.
 */
void lifecycle_device_id_get(lifecycle_device_id_t *device_id);

/**
 * Get the hardware revision.
 *
 * @param[out] hw_rev Hardware revision.
 */
void lifecycle_hw_rev_get(lifecycle_hw_rev_t *hw_rev);

/**
 * Determine if the device identification number subfield of the Device Id is
 * equal to the supplied DIN.
 *
 * @returns kHardenedBoolTrue if equal, kHardenedBoolFalse if not equal.
 */
hardened_bool_t lifecycle_din_eq(lifecycle_device_id_t *id, uint32_t *din);

typedef enum lifecycle_status_word {
  kLifecycleStatusWordRomExtVersion = 0,
  kLifecycleStatusWordRomExtSecVersion = 1,
  kLifecycleStatusWordOwnerVersion = 2,
  kLifecycleStatusWordDeviceStatus = 3,
} lifecycle_status_word_t;

/**
 * Device Status.
 *
 * These identifiers refer to boot stages observed during production.
 * Firmware will program these identifiers into the lifecycle controller's
 * TRANSITION_TOKEN registers so they can be read out via JTAG during the
 * manufacturing process.
 */
typedef enum lifecycle_device_status {
  /** Default 0: an invalid state. */
  kLifecycleDeviceStatusDefault = 0,
  /**
   * ROM_EXT:
   * - OK:  0x00000001 - 0x00000FFF
   * - Err: 0x10000001 - 0x10000FFF
   */
  kLifecycleDeviceStatusRomExtStart = 0x1,
  /**
   * Perso Firmware:
   * - OK:  0x00001000 - 0x00001FFF
   * - Err: 0x10001000 - 0x10001FFF
   */
  kLifecycleDeviceStatusPersoStart = 0x1000,
  /**
   * Owner (application) Firmware:
   * - OK:  0x00002000 - 0x00002FFF
   * - Err: 0x10002000 - 0x10002FFF
   */
  kLifecycleDeviceStatusOwnerStart = 0x2000,
} lifecycle_device_status_t;

/**
 * Claim the lifecycle controller transition interface.
 *
 * @param claim Either kMultiBitBool8True to claim or kMultiBitBool8False to
 *              release.
 * @return Whether or not the interface was claimed.
 */
bool lifecycle_claim(uint32_t claim);

/**
 * Write the boot stage information into the TRANSITION_TOKEN registers.
 *
 * Silicon_creator information is written to token registers 0-1.  Silicon_owner
 * information is written to token registers 2-3.
 */
void lifecycle_set_status(lifecycle_status_word_t word, uint32_t value);

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_LIFECYCLE_H_
