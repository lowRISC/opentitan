// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_RANDOM_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_RANDOM_H_

#include <stdint.h>

/**
 * Generate a pseudo-random unsigned integer.
 *
 * For testing purposes, a simple LFSR generates random numbers starting with
 * a known seed.
 * @return A pseudo-random 32-bit value.
 */
uint32_t random_gen32(void);

/**
 * Generate a random unsigned integer within a given range.
 *
 * This function invokes `random_gen32()` and restricts the returned value to
 * be within the supplied range, inclusive of the range limits. Note that PRNG
 * is not expected to produce a uniform distribution of values within the given
 * range.
 * @param min The lower limit of the range.
 * @param max The upper limit of the range.
 * @return The computed random value within the supplied range.
 */
uint32_t random_gen32_range(uint32_t min, uint32_t max);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_RANDOM_H_
