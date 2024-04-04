// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/hash.h"
#include "sw/device/lib/crypto/include/kdf.h"
#include "sw/device/lib/crypto/include/mac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// The autogen rule that creates this header creates it in a directory named
// after the rule, then manipulates the include path in the
// cc_compilation_context to include that directory, so the compiler will find
// the version of this file matching the Bazel rule under test.
#include "kdf_testvectors.h"

// Global pointer to the current test vector.
static kdf_kmac_test_vector_t *current_test_vector = NULL;

/**
 * Get the mode for KMAC based on test operation.
 *
 * @param test_operation Security strength of KMAC.
 * @param[out] mode KMAC mode enum value.
 */
status_t get_kmac_mode(kdf_test_operation_t test_operation,
                       otcrypto_kmac_mode_t *mode) {
  switch (test_operation) {
    case kKdfTestOperationKmac128:
      *mode = kOtcryptoKmacModeKmac128;
      break;
    case kKdfTestOperationKmac256:
      *mode = kOtcryptoKmacModeKmac256;
      break;
    default:
      LOG_INFO("Invalid test operation is given for KDF-KMAC");
      return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}

/**
 * Run the test pointed to by `current_test_vector`.
 */
static status_t run_test_vector(void) {
  // Below, `km` prefix refers to keying_material, and
  // `kdk` prefix refers to key derivation key
  size_t km_key_length = current_test_vector->keying_material.config.key_length;

  size_t km_num_words = km_key_length / sizeof(uint32_t);
  if (km_key_length % sizeof(uint32_t) != 0) {
    km_num_words++;
  }
  uint32_t km_buffer[km_num_words];

  otcrypto_kmac_mode_t mode;
  TRY(get_kmac_mode(current_test_vector->test_operation, &mode));

  otcrypto_blinded_key_t keying_material = {
      .config =
          {
              // The following key_mode is a dummy placeholder. It does not
              // necessarily match the `key_length`.
              .key_mode = kOtcryptoKeyModeKdfKmac128,
              .key_length = km_key_length,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
              .exportable = kHardenedBoolTrue,
          },
      .keyblob = km_buffer,
      .keyblob_length = 2 * km_key_length};

  // Populate `checksum` and `config.security_level` fields.
  current_test_vector->key_derivation_key.checksum =
      integrity_blinded_checksum(&current_test_vector->key_derivation_key);

  TRY(otcrypto_kdf_kmac(
      current_test_vector->key_derivation_key, mode, current_test_vector->label,
      current_test_vector->context, km_key_length, &keying_material));

  HARDENED_CHECK_EQ(integrity_blinded_key_check(&keying_material),
                    kHardenedBoolTrue);

  // At the moment, the function `kmac_kmac_128` called under the hood does not
  // return the digest in 2 shares. Therefore we can simply compare the first
  // share of the result from the test vector, since the second share is always
  // 0.
  TRY_CHECK_ARRAYS_EQ((uint8_t *)keying_material.keyblob,
                      (uint8_t *)current_test_vector->keying_material.keyblob,
                      km_key_length);
  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();
bool test_main(void) {
  LOG_INFO("Testing cryptolib KDF-KMAC driver.");

  // Initialize the core with default parameters
  CHECK_STATUS_OK(entropy_complex_init());
  CHECK_STATUS_OK(kmac_hwip_default_configure());

  status_t test_result = OK_STATUS();
  for (size_t i = 0; i < ARRAYSIZE(kKdfTestVectors); i++) {
    current_test_vector = &kKdfTestVectors[i];
    LOG_INFO("Running test %d of %d, test vector identifier: %s", i + 1,
             ARRAYSIZE(kKdfTestVectors),
             current_test_vector->vector_identifier);
    EXECUTE_TEST(test_result, run_test_vector);
  }
  return status_ok(test_result);
}
