// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/status.h"

/**
 * Basic mock of the entropy complex driver.
 *
 * Enables on-host unit tests of code that uses `entropy_complex_check()`.
 */

namespace test {
extern "C" {

const entropy_seed_material_t kEntropyEmptySeed = {
    .len = 0,
    .data = {0},
};

status_t entropy_complex_init(void) { return OTCRYPTO_OK; }

status_t entropy_complex_check(void) { return OTCRYPTO_OK; }

status_t entropy_csrng_instantiate(
    hardened_bool_t disable_trng_input,
    const entropy_seed_material_t *seed_material) {
  return OTCRYPTO_OK;
}

status_t entropy_csrng_reseed(hardened_bool_t disable_trng_input,
                              const entropy_seed_material_t *seed_material) {
  return OTCRYPTO_OK;
}

status_t entropy_csrng_update(const entropy_seed_material_t *seed_material) {
  return OTCRYPTO_OK;
}

status_t entropy_csrng_generate_start(
    const entropy_seed_material_t *seed_material, size_t len) {
  return OTCRYPTO_OK;
}

status_t entropy_csrng_generate_data_get(uint32_t *buf, size_t len,
                                         hardened_bool_t fips_check) {
  // This mock does not support actually generating random values.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

status_t entropy_csrng_generate(const entropy_seed_material_t *seed_material,
                                uint32_t *buf, size_t len,
                                hardened_bool_t fips_check) {
  // This mock does not support actually generating random values.
  return OTCRYPTO_NOT_IMPLEMENTED;
}

status_t entropy_csrng_uninstantiate(void) { return OTCRYPTO_OK; }
}
}  // namespace test
