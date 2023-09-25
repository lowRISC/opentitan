// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/drbg.h"

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('r', 'b', 'g')

/**
 * Construct seed material for the CSRNG.
 *
 * Returns `OTCRYPTO_BAD_ARGS` if the provided value is longer than the entropy
 * complex can absorb. If the value is shorter, it will be padded with zeroes.
 *
 * This operation is not constant-time relative to `value.len`.
 *
 * @param value Seed data.
 * @param[out] seed_material Resulting entropy complex seed.
 * @return OK or error.
 */
static crypto_status_t seed_material_construct(
    crypto_const_byte_buf_t value, entropy_seed_material_t *seed_material) {
  if (value.len > kEntropySeedBytes) {
    return OTCRYPTO_BAD_ARGS;
  }

  size_t nwords = (value.len + sizeof(uint32_t) - 1) / sizeof(uint32_t);
  seed_material->len = nwords;

  // Initialize the set words to zero.
  memset(seed_material->data, 0, nwords * sizeof(uint32_t));

  if (value.len == 0) {
    return OTCRYPTO_OK;
  }

  // Copy seed data.
  // TODO(#17711) Change to `hardened_memcpy`.
  memcpy(seed_material->data, value.data, value.len);

  return OTCRYPTO_OK;
}

/**
 * XOR the entropy seed with another value.
 *
 * Returns `OTCRYPTO_BAD_ARGS` if the provided value is longer than the seed.
 * If the value is shorter, only the prefix will be XOR'ed.
 *
 * This operation is not constant-time relative to `value.len`.
 *
 * @param value Value to XOR with seed data.
 * @param seed_material Entropy complex seed, modified in-place.
 * @return OK or error.
 */
static crypto_status_t seed_material_xor(
    crypto_const_byte_buf_t value, entropy_seed_material_t *seed_material) {
  if (value.len > kEntropySeedBytes) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (value.len == 0) {
    return OTCRYPTO_OK;
  }

  // Copy into a word-aligned buffer. Using a word-wise XOR is slightly safer
  // from a side channel perspective than byte-wise.
  size_t nwords = (value.len + sizeof(uint32_t) - 1) / sizeof(uint32_t);
  uint32_t value_words[nwords];
  value_words[nwords - 1] = 0;
  memcpy(value_words, value.data, value.len);

  // XOR with seed value.
  for (size_t i = 0; i < nwords; i++) {
    seed_material->data[i] ^= value_words[i];
  }

  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_drbg_instantiate(
    crypto_const_byte_buf_t perso_string) {
  // Check for NULL pointers or bad length.
  if (perso_string.len != 0 && perso_string.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  entropy_seed_material_t seed_material;
  seed_material_construct(perso_string, &seed_material);

  HARDENED_TRY(entropy_csrng_uninstantiate());
  return entropy_csrng_instantiate(/*disable_trng_input=*/kHardenedBoolFalse,
                                   &seed_material);
}

crypto_status_t otcrypto_drbg_reseed(crypto_const_byte_buf_t additional_input) {
  // Check for NULL pointers or bad length.
  if (additional_input.len != 0 && additional_input.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  entropy_seed_material_t seed_material;
  seed_material_construct(additional_input, &seed_material);

  return entropy_csrng_reseed(/*disable_trng_input=*/kHardenedBoolFalse,
                              &seed_material);
}

crypto_status_t otcrypto_drbg_manual_instantiate(
    crypto_const_byte_buf_t entropy, crypto_const_byte_buf_t perso_string) {
  // Check for NULL pointers or bad length.
  if (perso_string.len != 0 && perso_string.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (entropy.data == NULL || entropy.len != kEntropySeedBytes) {
    return OTCRYPTO_BAD_ARGS;
  }

  entropy_seed_material_t seed_material;
  seed_material_construct(entropy, &seed_material);
  seed_material_xor(perso_string, &seed_material);

  HARDENED_CHECK_EQ(seed_material.len, kEntropySeedWords);

  return entropy_csrng_instantiate(/*disable_trng_input=*/kHardenedBoolTrue,
                                   &seed_material);
}

crypto_status_t otcrypto_drbg_manual_reseed(
    crypto_const_byte_buf_t entropy, crypto_const_byte_buf_t additional_input) {
  // Check for NULL pointers or bad length.
  if (additional_input.len != 0 && additional_input.data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (entropy.data == NULL || entropy.len != kEntropySeedBytes) {
    return OTCRYPTO_BAD_ARGS;
  }

  entropy_seed_material_t seed_material;
  seed_material_construct(entropy, &seed_material);
  seed_material_xor(additional_input, &seed_material);

  HARDENED_CHECK_EQ(seed_material.len, kEntropySeedWords);

  return entropy_csrng_reseed(/*disable_trng_input=*/kHardenedBoolTrue,
                              &seed_material);
}

/**
 * Common function for random-bit generation.
 *
 * Used for both `otcrypto_drbg_generate` and `otcrypto_drbg_manual_generate`,
 * which have the same implementation except for one flag that determines
 * whether we check that the flag for FIPS compatibility is true.
 *
 * @param additional_input Additional input to DRBG
 * @param fips_check Whether to check FIPS hardware flags
 * @param[out] drbg_output Buffer for output
 * @return Result status; OK or error
 */
static crypto_status_t generate(hardened_bool_t fips_check,
                                crypto_const_byte_buf_t additional_input,
                                crypto_word32_buf_t *drbg_output) {
  if (drbg_output == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
  if (drbg_output->len == 0) {
    // Nothing to do.
    return OTCRYPTO_OK;
  }
  if ((additional_input.len != 0 && additional_input.data == NULL) ||
      drbg_output->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  entropy_seed_material_t seed_material;
  seed_material_construct(additional_input, &seed_material);
  HARDENED_TRY(entropy_csrng_generate(&seed_material, drbg_output->data,
                                      drbg_output->len, fips_check));

  return OTCRYPTO_OK;
}

crypto_status_t otcrypto_drbg_generate(crypto_const_byte_buf_t additional_input,
                                       crypto_word32_buf_t *drbg_output) {
  return generate(/*fips_check=*/kHardenedBoolTrue, additional_input,
                  drbg_output);
}

crypto_status_t otcrypto_drbg_manual_generate(
    crypto_const_byte_buf_t additional_input,
    crypto_word32_buf_t *drbg_output) {
  return generate(/*fips_check=*/kHardenedBoolFalse, additional_input,
                  drbg_output);
}

crypto_status_t otcrypto_drbg_uninstantiate(void) {
  return entropy_csrng_uninstantiate();
}
