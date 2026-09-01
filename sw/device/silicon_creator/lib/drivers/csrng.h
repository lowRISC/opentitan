// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_CSRNG_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_CSRNG_H_

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/silicon_creator/lib/error.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Initializes and enables the CSRNG module directly for software application
 * access.
 *
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t csrng_enable(void);

/**
 * Instantiates the CSRNG SW instance using hardware entropy source (TRNG).
 *
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t csrng_instantiate(void);

/**
 * Reads random words directly from CSRNG's SW application interface.
 *
 * @param[out] dest Output buffer to store generated random words.
 * @param num_words Number of 32-bit words to generate and read.
 * @return Result of the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t csrng_read_words(uint32_t *dest, size_t num_words);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_CSRNG_H_
