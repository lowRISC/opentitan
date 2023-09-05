// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/keymgr.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

// Key diversification data for testing
static const keymgr_diversification_t kTestDiversification = {
    .salt =
        {
            0x00112233,
            0x44556677,
            0x8899aabb,
            0xccddeeff,
            0x00010203,
            0x04050607,
            0x08090a0b,
            0x0c0d0e0f,
        },
    .version = 0x9,
};

/**
 * Setup keymgr and entropy complex.
 *
 * Run this test before any others.
 */
status_t test_setup(void) {
  // Initialize the key manager and advance to OwnerRootKey state.
  dif_keymgr_t keymgr;
  dif_kmac_t kmac;
  TRY(keymgr_testutils_startup(&keymgr, &kmac));
  TRY(keymgr_testutils_advance_state(&keymgr, &kOwnerIntParams));
  TRY(keymgr_testutils_advance_state(&keymgr, &kOwnerRootKeyParams));
  TRY(keymgr_testutils_check_state(&keymgr, kDifKeymgrStateOwnerRootKey));

  // Initialize entropy complex, which the key manager uses to clear sideloaded
  // keys. The `keymgr_testutils_startup` function restarts the device, so this
  // should happen afterwards.
  return entropy_complex_init();
}

/**
 * Test generating a single software-visible key.
 *
 * This test just checks that the key generation process finished without
 * errors, without performing any validation on the key.
 */
status_t sw_single_key_test(void) {
  keymgr_output_t key;
  return keymgr_generate_key_sw(kTestDiversification, &key);
}

/**
 * Test generating a single sideloaded AES key.
 *
 * This test just checks that the key generation process finished without
 * errors, without actually attempting to use the key.
 */
status_t aes_basic_test(void) {
  return keymgr_generate_key_aes(kTestDiversification);
}

/**
 * Test generating a single sideloaded KMAC key.
 *
 * This test just checks that the key generation process finished without
 * errors, without actually attempting to use the key.
 */
status_t kmac_basic_test(void) {
  return keymgr_generate_key_kmac(kTestDiversification);
}

/**
 * Test generating a single sideloaded OTBN key.
 *
 * This test just checks that the key generation process finished without
 * errors, without actually attempting to use the key.
 */
status_t otbn_basic_test(void) {
  return keymgr_generate_key_otbn(kTestDiversification);
}

/**
 * Check whether two key manager output values are equivalent.
 *
 * Unmasks both keys and compares their unmasked values; masking should not
 * affect this comparison.
 *
 * @param key1 First key manager output.
 * @param key2 Second key manager output.
 * @return true if the keys are equivalent, false otherwise.
 */
static bool output_equiv(keymgr_output_t key1, keymgr_output_t key2) {
  for (size_t i = 0; i < kKeymgrOutputShareNumWords; i++) {
    uint32_t word1 = key1.share0[i] ^ key1.share1[i];
    uint32_t word2 = key2.share0[i] ^ key2.share1[i];
    if (word1 != word2) {
      return false;
    }
  }
  return true;
}

/**
 * Test generating software-visible keys with different salts.
 *
 * Different salts should produce different keys; the same salt should produce
 * the same key but with different masking.
 */
status_t sw_keys_change_salt_test(void) {
  // Copy the test data into a mutable structure.
  keymgr_diversification_t div;
  memcpy(div.salt, kTestDiversification.salt, sizeof(div.salt));
  div.version = kTestDiversification.version;

  // Generate a key.
  keymgr_output_t key1;
  TRY(keymgr_generate_key_sw(div, &key1));

  // Change the salt and generate the key again.
  div.salt[0]++;
  keymgr_output_t key2;
  TRY(keymgr_generate_key_sw(div, &key2));

  // Check that the keys are distinct.
  TRY_CHECK(!output_equiv(key1, key2));

  // Change the salt back to its original value and generate a third time.
  div.salt[0]--;
  keymgr_output_t key3;
  TRY(keymgr_generate_key_sw(div, &key3));

  // Check that the key is the equivalent to the first key when unmasked.
  TRY_CHECK(output_equiv(key1, key3));

  // Check that the masking on the equivalent keys is different.
  TRY_CHECK_ARRAYS_NE(key1.share0, key2.share0, sizeof(key1.share0));

  return OK_STATUS();
}

/**
 * Test generating software-visible keys with different versions.
 *
 * Different versions should produce different keys; the same version should
 * produce the same key but with different masking.
 */
status_t sw_keys_change_version_test(void) {
  // Copy the test data into a mutable structure.
  keymgr_diversification_t div;
  memcpy(div.salt, kTestDiversification.salt, sizeof(div.salt));
  div.version = kTestDiversification.version;

  // Generate a key.
  keymgr_output_t key1;
  TRY(keymgr_generate_key_sw(div, &key1));

  // Change the version and generate the key again.
  div.version++;
  keymgr_output_t key2;
  TRY(keymgr_generate_key_sw(div, &key2));

  // Check that the keys are distinct.
  TRY_CHECK(!output_equiv(key1, key2));

  // Change the version back to its original value and generate a third time.
  div.version--;
  keymgr_output_t key3;
  TRY(keymgr_generate_key_sw(div, &key3));

  // Check that the key is the equivalent to the first key when unmasked.
  TRY_CHECK(output_equiv(key1, key3));

  // Check that the masking on the equivalent keys is different.
  TRY_CHECK_ARRAYS_NE(key1.share0, key2.share0, sizeof(key1.share0));

  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  static status_t result;

  EXECUTE_TEST(result, test_setup);
  EXECUTE_TEST(result, sw_single_key_test);
  EXECUTE_TEST(result, sw_keys_change_salt_test);
  EXECUTE_TEST(result, sw_keys_change_version_test);
  EXECUTE_TEST(result, aes_basic_test);
  EXECUTE_TEST(result, kmac_basic_test);
  EXECUTE_TEST(result, otbn_basic_test);

  return status_ok(result);
}
