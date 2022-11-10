// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_RAND_TESTUTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_RAND_TESTUTILS_H_

#include <stdint.h>

#include "sw/device/lib/testing/rv_core_ibex_testutils.h"

/**
 * A random number generator testutil type.
 *
 * Provides ability to control and maintain a random number generator. A random
 * number is produced via a mix of hardware-based (using on-device entropy
 * from rv_core_ibex random registers) and software-based (an LFSR-based PRNG)
 * approaches. The initial seed value for the PRNG is fetched from the
 * hardware. Following that, the PRNG kicks in and supplies random values
 * sought by the test. After a number of PRNG cycles, the LFSR can be freshly
 * reseeded from the hardware. If this frequency is set to 0, then the PRNG is
 * rendered disabled and random data is always fetched from the hardware.
 *
 * The software PRNG is faster because it consumes very few cycles compared to
 * the hardware - it helps improve the simulation time.
 */
typedef struct rand_testutils_rng {
  /**
   * An rv_core_ibex DIF handle.
   */
  dif_rv_core_ibex_t *rv_core_ibex;
  /**
   * The timeout in microseconds for fetching data from the hardware.
   */
  uint32_t entropy_fetch_timeout_usec;
  /**
   * The PRNG LFSR.
   */
  uint32_t lfsr;
  /**
   * The PRNG polynomial co-efficients.
   */
  uint32_t polynomial_coefficients;
  /**
   * The PRNG LFSR reseed frequency.
   */
  uint32_t reseed_frequency;
  /**
   * The LFSR operation counter. Resets on every reseed.
   */
  uint32_t op_counter;
} rand_testutils_rng_t;

/**
 * A global random number generator testutil handle.
 */
extern rand_testutils_rng_t rand_testutils_rng_ctx;

/**
 * Initializes and returns a random number generator testutil handle.
 *
 * @param rv_core_ibex An rv_core_ibex DIF handle.
 * @return The initialized timeout value.
 */
rand_testutils_rng_t rand_testutils_init(dif_rv_core_ibex_t *rv_core_ibex);

/**
 * Reseeds the PRNG LFSR.
 *
 * The LFSR value is updated later, when the caller fetches the next random
 * data.
 *
 * Uses the global random number generator testutil handle
 * `rand_testutils_rng_ctx` which is initialized in ottf_main().
 */
inline void rand_testutils_reseed(void) {
  rand_testutils_rng_ctx.op_counter = UINT32_MAX;
}

/**
 * Returns a random unsigned integer.
 *
 * The random number is sourced either from the LFSR-based PRNG or from the
 * hardware, depending on the lobal random number generator testutil context
 * settings.
 * @return A pseudo-random 32-bit value.
 */
uint32_t rand_testutils_gen32(void);

/**
 * Returns a random unsigned integer within a given range.
 *
 * This function invokes `rand_testutils_gen32()` and restricts the returned
 * value to be within the supplied range, inclusive of the range limits. Note
 * that a uniform distribution of values within the given range is not
 * guaranteed.
 * @param min The lower limit of the range.
 * @param max The upper limit of the range.
 * @return The computed random value within the supplied range.
 */
uint32_t rand_testutils_gen32_range(uint32_t min, uint32_t max);

/** Shuffles an arbitrary array of elements.
 *
 * The shuffling occurs in-place. The reseeding of the LFSR is temporarily
 * turned off to allow faster runtime performance.
 * @param array Pointer to the array being shuffled.
 * @param size The size of each element in the array.
 * @param length The number of elements in the array.
 */
void rand_testutils_shuffle(void *array, size_t size, size_t length);

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_RAND_TESTUTILS_H_
