// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/key_transport.h"
#include "sw/device/lib/crypto/include/kmac_kdf.h"
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
 * Run the test pointed to by `current_test_vector`.
 */
static status_t run_test_vector(void) {
  // Below, `km` prefix refers to output_key_material, and
  // `kdk` prefix refers to key derivation key
  size_t km_num_words = current_test_vector->expected_output.len;
  uint32_t km_buffer[2 * km_num_words];

  otcrypto_blinded_key_t output_key_material = {
      .config =
          {
              // The following key_mode is a dummy placeholder. It does not
              // necessarily match the `key_length`.
              .key_mode = kOtcryptoKeyModeKdfKmac128,
              .version = kOtcryptoLibVersion1,
              .key_length = km_num_words * sizeof(uint32_t),
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
              .exportable = kHardenedBoolTrue,
          },
      .keyblob = km_buffer,
      .keyblob_length = sizeof(km_buffer),
  };

  // Populate `checksum` and `config.security_level` fields.
  current_test_vector->key_derivation_key.checksum =
      integrity_blinded_checksum(&current_test_vector->key_derivation_key);

  TRY(otcrypto_kmac_kdf(&current_test_vector->key_derivation_key,
                        current_test_vector->label,
                        current_test_vector->context, &output_key_material));

  HARDENED_CHECK_EQ(integrity_blinded_key_check(&output_key_material),
                    kHardenedBoolTrue);

  // Export the derived blinded key.
  uint32_t km_share0[km_num_words];
  uint32_t km_share1[km_num_words];
  TRY(otcrypto_export_blinded_key(
      &output_key_material,
      (otcrypto_word32_buf_t){.data = km_share0, .len = ARRAYSIZE(km_share0)},
      (otcrypto_word32_buf_t){.data = km_share1, .len = ARRAYSIZE(km_share1)}));

  // Unmask the derived key and compare to the expected value.
  uint32_t actual_output[km_num_words];
  for (size_t i = 0; i < ARRAYSIZE(actual_output); i++) {
    actual_output[i] = km_share0[i] ^ km_share1[i];
  }
  TRY_CHECK_ARRAYS_EQ(actual_output, current_test_vector->expected_output.data,
                      km_num_words);
  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();
bool test_main(void) {
  LOG_INFO("Testing cryptolib KMAC-KDF driver.");

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
