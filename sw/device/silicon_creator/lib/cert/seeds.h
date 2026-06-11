// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_SEEDS_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_SEEDS_H_

#include <stdint.h>

#include "sw/device/silicon_creator/lib/error.h"

/**
 * Loads the factory attestation keygen seed from the flash info page.
 *
 * @param additional_seed_idx Index of the seed (0 for UDS, 1 for CDI_0, etc.)
 * @param[out] seed Output buffer of size kAttestationSeedWords (10 words / 320
 * bits).
 * @return Error code.
 */
rom_error_t load_attestation_keygen_seed(uint32_t additional_seed_idx,
                                         uint32_t *seed);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_SEEDS_H_
