// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
#ifndef OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_ENTROPY_H_
#define OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_ENTROPY_H_

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/status.h"

#ifdef __cplusplus
extern "C" {
#endif

/**
 * Seed material as specified in NIST SP 800-90Ar1 section 10.2.1.3.1. Up to 12
 * words of seed material can be provided using this interface.
 */
typedef struct entropy_seed_material {
  /**
   * Number of words set in `data`. CSRNG will extend the `data` to zeros if the
   * provided value is less than 12.
   */
  size_t len;
  /**
   * Seed material in unsigned word format.
   */
  uint32_t data[12];
} entropy_seed_material_t;

/**
 * Configures the entropy complex in continuous mode.
 *
 * The complex is configured in continuous mode with FIPS mode enabled. This is
 * the default operational mode of the entropy_src, csrng, edn0 and edn1 blocks.
 *
 * @return Operation status in `status_t` format.
 */
OT_WARN_UNUSED_RESULT
status_t entropy_complex_init(void);

/**
 * Instantiate the SW CSRNG with a new seed value.
 *
 * SW CSRNG refers to the CSRNG hardware instance available for software use.
 *
 * @param disable_trng_input Set to kHardenedTrue to disable the random seed
 * data provided by hardware. This enables the use of the CSRNG in deterministic
 * mode.
 * @param seed_material Data used to seed the CSRNG. XOR'ed entropy provided by
 * hardware when `disable_trng_input` is set to `kHardenedFalse`, otherwise used
 * directly as the seed.
 * @return Operation status in `status_t` format.
 */
OT_WARN_UNUSED_RESULT
status_t entropy_csrng_instantiate(
    hardened_bool_t disable_trng_input,
    const entropy_seed_material_t *seed_material);

/**
 * Reseed the SW CSRNG.
 *
 * @param disable_trng_input Set to kHardenedTrue to disable the entropy
 * provided by hardware.
 * @param seed_material Data used to reseed the CSRNG. XOR'ed with entropy
 * provided by hardware when `disable_trng_input` is set to `kHardenedFalse`,
 * otherwise used directly as the seed
 * @return Operation status in `status_t` format.
 */
OT_WARN_UNUSED_RESULT
status_t entropy_csrng_reseed(hardened_bool_t disable_trng_input,
                              const entropy_seed_material_t *seed_material);

/**
 * Update the SW CSRNG state.
 *
 * This command does not update the CSRNG internal reseed counter.
 *
 * @param seed_material Additional data used in the CSRNG update operation.
 * There is no additional entropy loaded from hardware.
 * @return Operation status in `status_t` format.
 */
OT_WARN_UNUSED_RESULT
status_t entropy_csrng_update(const entropy_seed_material_t *seed_material);

/**
 * Request data from the SW CSRNG.
 *
 * Use `entropy_csrng_generate_data_get()` to read the data from the CSRNG
 * output buffer.
 *
 * See `entropy_csrng_generate()` for requesting and reading the CSRNG output in
 * a single call.
 *
 * @param seed_material Additional data used in the CSRNG generate operation.
 * There is no additional entropy loaded from hardware.
 * @param len Number of uint32_t words to generate.
 * @return Operation status in `status_t` format.
 */
OT_WARN_UNUSED_RESULT
status_t entropy_csrng_generate_start(
    const entropy_seed_material_t *seed_material, size_t len);

/**
 * Read SW CSRNG output.
 *
 * Requires the `entropy_csrng_generate_start()` function to be called in
 * advance, otherwise the function will block indefinitely.
 *
 * @param buf A buffer to fill with words from the CSRNG output buffer.
 * @param len The number of words to read into `buf`.
 * @return Operation status in `status_t` format.
 */
OT_WARN_UNUSED_RESULT
status_t entropy_csrng_generate_data_get(uint32_t *buf, size_t len);

/**
 * Request and read data from the SW CSRNG.
 *
 * @param seed_material Additional data used in the CSRNG generate operation.
 * There is not additional entropy loaded from hardware.
 * @param buf A buffer to fill with words from the CSRNG output buffer.
 * @param len The number of words to read into `buf`.
 * @return Operation status in `status_t` format. OutOfRange if the `len`
 * parameter results in a 128bit block level size greater than 0x800.
 */
OT_WARN_UNUSED_RESULT
status_t entropy_csrng_generate(const entropy_seed_material_t *seed_material,
                                uint32_t *buf, size_t len);

/**
 * Uninstantiate the SW CSRNG.
 *
 * Thia operation effectively resets the state of the SW CSRNG instance,
 * clearing any errors that it may have encountered due to bad command syntax or
 * entropy source failures.
 *
 * @return Operation status in `status_t` format.
 */
OT_WARN_UNUSED_RESULT
status_t entropy_csrng_uninstantiate(void);

#ifdef __cplusplus
}
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_CRYPTO_DRIVERS_ENTROPY_H_
