// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/randomness_quality.h"

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/testing/test_framework/check.h"

enum {
  /**
   * Thresholds for the monobit test (alpha=0.05), 5% false negative rate.
   *
   * Based on the Handbook of Applied Cryptography, Table 5.2 and section
   * 5.4.4. To avoid floating-point arithmetic we represent the threshold value
   * as a fraction.
   */
  kMonobitFivePercentThresholdNumerator = 38415,
  kMonobitFivePercentThresholdDenominator = 10000,
  /**
   * Thresholds for the monobit test (alpha=0.01), 1% false negative rate.
   *
   * Based on the Handbook of Applied Cryptography, Table 5.2 and section
   * 5.4.4. To avoid floating-point arithmetic we represent the threshold value
   * as a fraction.
   */
  kMonobitOnePercentThresholdNumerator = 66349,
  kMonobitOnePercentThresholdDenominator = 10000,
};

/**
 * Get the square of the difference of two numbers.
 *
 * @param a First operand.
 * @param b Second operand.
 * @return Result, (a - b)^2
 */
static uint64_t diff_squared(uint64_t a, uint64_t b) {
  if (a <= b) {
    return (b - a) * (b - a);
  }
  return (a - b) * (a - b);
}

status_t randomness_quality_monobit_test(
    uint8_t *data, size_t len, randomness_quality_threshold_t threshold) {
  // Guard against overflow in the bit-count.
  TRY_CHECK(len <= UINT32_MAX);

  // Count the number of zeroes and the number of ones in the data.
  uint32_t num_ones = 0;
  uint32_t num_zeroes = 0;
  for (size_t i = 0; i < len; i++) {
    uint8_t byte = data[i];
    for (size_t j = 0; j < 8; j++) {
      num_ones += byte & 1;
      num_zeroes += (byte ^ 1) & 1;
      byte >>= 1;
    }
  }

  // Numerical result of the test is (#zeroes - #ones)^2 / bitlen.
  uint64_t numerator = diff_squared(num_ones, num_zeroes);
  uint64_t denominator = len * 8;

  // Retrieve the threshold values.
  uint64_t threshold_numerator = 0;
  uint64_t threshold_denominator = 1;
  switch (threshold) {
    case kRandomnessQualityThresholdFivePercent: {
      threshold_numerator = kMonobitFivePercentThresholdNumerator;
      threshold_denominator = kMonobitFivePercentThresholdDenominator;
      break;
    }
    case kRandomnessQualityThresholdOnePercent: {
      threshold_numerator = kMonobitOnePercentThresholdNumerator;
      threshold_denominator = kMonobitOnePercentThresholdDenominator;
      break;
    }
    default:
      return INVALID_ARGUMENT();
  }

  // Return true if the result value is <= to the threshold.
  uint64_t lhs = (numerator * threshold_denominator);
  uint64_t rhs = (threshold_numerator * denominator);
  TRY_CHECK(lhs <= rhs);

  return OK_STATUS();
}
