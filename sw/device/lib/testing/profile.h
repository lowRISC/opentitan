// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_PROFILE_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_PROFILE_H_

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * Start a cycle-count timing profile.
 *
 * Basic usage:
 *   uint64_t t_start = profile_start();
 *   // Do some stuff
 *   uint32_t cycles = profile_end(t_start);
 *   LOG_INFO("Some stuff took %d cycles.", cycles);
 *
 * You can run multiple profiles at once by simply calling `profile_start`
 * repeatedly.
 *
 * @return Ibex cycle count at start time.
 */
uint64_t profile_start();

/**
 * End a cycle-count timing profile.
 *
 * In typical usage, `t_start` is something that was previously returned from
 * `profile_start()`.
 *
 * @param t_start Cycle count at profile start time.
 * @return Number of cycles between t_start and current Ibex cycle count.
 */
uint32_t profile_end(uint64_t t_start);

/**
 * End a cycle-count timing profile and print a message with timing data.
 *
 * In typical usage, `t_start` is something that was previously returned from
 * `profile_start()`.
 *
 * @param t_start Cycle count at profile start time.
 * @param name Name of the profile, for printing.
 * @return Number of cycles between t_start and current Ibex cycle count.
 */
uint32_t profile_end_and_print(uint64_t t_start, char *name);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_PROFILE_H_
