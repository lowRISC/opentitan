// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SCA_LIB_PRNG_H_
#define OPENTITAN_SW_DEVICE_SCA_LIB_PRNG_H_

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * @file
 * @brief PRNG for side-channel analysis.
 *
 * This library provides a Mersenne Twister PRNG that can be used to generate
 * random plaintexts on the device. Generating random plaintexts on the device
 * eliminates the overhead of sending them from the host and can significantly
 * improve capture rate. The host must use the same PRNG to be able to compute
 * the plaintext and the ciphertext of each trace.
 *
 * TODO(alphan): Replace this with a more efficient PRNG after updating
 * host-side code.
 */

/**
 * Initializes the random number generator.
 *
 * @param seed Seed to initalize with.
 */
void prng_seed(uint32_t seed);

/**
 * Generates a random byte.
 *
 * The behavior of this function matches the behavior of `random.randint(0,
 * 255)` in python, which is used by ChipWhisperer's `ktp.next()`.
 *
 * @return A random byte.
 */
uint8_t prng_rand_byte(void);

/**
 * Fills a buffer with random bytes.
 *
 * The behavior of this function matches the behavior of `random.randint(0,
 * 255)` in python, which is used by ChipWhisperer's `ktp.next()`.
 *
 * @param[out] buffer     A buffer.
 * @param      buffer_len Size of the buffer.
 *
 * @return A random byte.
 */
void prng_rand_bytes(uint8_t *buffer, size_t buffer_len);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_SCA_LIB_PRNG_H_
