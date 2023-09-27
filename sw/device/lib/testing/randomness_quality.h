// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_RANDOMNESS_QUALITY_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_RANDOMNESS_QUALITY_H_

#include <stdint.h>

#include "sw/device/lib/base/status.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Test failure probability setting.
 *
 * The statistical tests in this file will always fail with some probability,
 * even on truly random data. Use these settings to toggle the threshold
 * values.
 */
typedef enum randomness_quality_threshold {
  /**
   * Set thresholds for a 5% failure rate on truly random data (alpha = 0.05).
   */
  kRandomnessQualityThresholdFivePercent,
  /**
   * Set thresholds for a 1% failure rate on truly random data (alpha = 0.01).
   */
  kRandomnessQualityThresholdOnePercent,
} randomness_quality_threshold_t;

/**
 * Monobit test from section 5.4.4 of the Handbook of Applied Cryptography.
 *
 * This test counts the number of zero and one bits in the data and expects the
 * number to be roughly similar.
 *
 * @param data Random data to check.
 * @param len Length of data.
 * @param threshold Test threshold setting.
 * @return OK if the test passes, a failure code otherwise.
 */
status_t randomness_quality_monobit_test(
    uint8_t *data, size_t len, randomness_quality_threshold_t threshold);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_RANDOMNESS_QUALITY_H_
