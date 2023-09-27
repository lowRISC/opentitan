// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/aes.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/keymgr.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/aes.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/keymgr_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('t', 's', 't')

// Key version data for testing.
static const uint32_t kKeyVersion = 0x9;

// Two distinct key salts for testing.
static const size_t kSaltNumWords = 7;
static const uint32_t kKeySalt1[7] = {
    0x00112233, 0x44556677, 0x8899aabb, 0xccddeeff,
    0x00010203, 0x04050607, 0x08090a0b,
};
static const uint32_t kKeySalt2[7] = {
    0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f,
    0x00112233, 0x44556677, 0x8899aabb,
};

// Indicates a sideloaded 256-bit AES-CTR key.
static const crypto_key_config_t kAesKeyConfig = {
    .version = kCryptoLibVersion1,
    .key_mode = kKeyModeAesCtr,
    .key_length = 256 / 8,
    .hw_backed = kHardenedBoolTrue,
    .security_level = kSecurityLevelLow,
};

// AES IV testing data.
static const uint32_t kAesIv[4] = {
    0xdeadbeef,
    0xdeadbeef,
    0xdeadbeef,
    0xdeadbeef,
};

// AES plaintext testing data.
static const uint32_t kAesPlaintextBlock[4] = {0};

/**
 * Convenience function to run AES with the test data.
 *
 * The salt should be exactly `kSaltNumWords` words long; the input and output
 * buffers should both match the size of `kAesPlaintextBlock` and be a multiple
 * of the block size (so no padding is needed).
 *
 * @param salt Key salt to use.
 * @param input Cipher input block(s).
 * @param[out] output Resulting output block(s).
 * @return OK or error.
 */
static status_t run_aes(aes_operation_t operation, const uint32_t *salt,
                        const uint32_t *input, uint32_t *output) {
  // Construct the key.
  uint32_t keyblob[kSaltNumWords + 1];
  keyblob[0] = kKeyVersion;
  memcpy(&keyblob[1], salt, kSaltNumWords * sizeof(uint32_t));
  crypto_blinded_key_t key = {
      .config = kAesKeyConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
      .checksum = 0,
  };
  key.checksum = integrity_blinded_checksum(&key);

  // Construct the IV.
  uint32_t iv_data[ARRAYSIZE(kAesIv)];
  memcpy(iv_data, kAesIv, sizeof(kAesIv));
  crypto_word32_buf_t iv = {
      .data = iv_data,
      .len = ARRAYSIZE(iv_data),
  };

  // Construct the input buffer.
  crypto_const_byte_buf_t input_buf = {
      .data = (const unsigned char *)input,
      .len = sizeof(kAesPlaintextBlock),
  };

  // Construct the output buffer.
  crypto_byte_buf_t output_buf = {
      .data = (unsigned char *)output,
      .len = sizeof(kAesPlaintextBlock),
  };

  return otcrypto_aes(&key, iv, kBlockCipherModeCtr, operation, input_buf,
                      kAesPaddingNull, output_buf);
}

/**
 * Convenience function to encrypt the test plaintext.
 *
 * The salt should be exactly `kSaltNumWords` words long; the output buffer
 * should match the size of `kAesPlaintextBlock`.
 *
 * @param salt Key salt to use.
 * @param[out] ciphertext Resulting encrypted output.
 * @return OK or error.
 */
static status_t encrypt(const uint32_t *salt, uint32_t *ciphertext) {
  return run_aes(kAesOperationEncrypt, salt, kAesPlaintextBlock, ciphertext);
}

/**
 * Convenience function to decrypt ciphertext.
 *
 * The salt should be exactly `kSaltNumWords` words long; the plaintext and
 * ciphertext buffers should both match the size of `kAesPlaintextBlock`.
 *
 * @param salt Key salt to use.
 * @param ciphertext Encrypted message.
 * @param[out] plaintext Resulting decrypted output.
 * @return OK or error.
 */
static status_t decrypt(const uint32_t *salt, const uint32_t *ciphertext,
                        uint32_t *plaintext) {
  return run_aes(kAesOperationDecrypt, salt, ciphertext, plaintext);
}

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
 * Test that a sideloaded AES key can be used.
 *
 * Loads a sideloaded key, then runs encryption and decryption using the key.
 */
status_t basic_encrypt_decrypt_test(void) {
  // Encrypt the test plaintext.
  uint32_t ciphertext1[ARRAYSIZE(kAesPlaintextBlock)];
  TRY(encrypt(kKeySalt1, ciphertext1));

  // Decrypt the ciphertext.
  uint32_t recovered_plaintext[ARRAYSIZE(kAesPlaintextBlock)];
  TRY(decrypt(kKeySalt1, ciphertext1, recovered_plaintext));

  // Check that the recovered plaintext matches the original plaintext.
  TRY_CHECK_ARRAYS_EQ(recovered_plaintext, kAesPlaintextBlock,
                      ARRAYSIZE(kAesPlaintextBlock));

  return OK_STATUS();
}

/**
 * Test that sideloaded AES keys are updated as expected.
 *
 * Different keys should produce different ciphertexts, and the same key
 * should produce the same ciphertext.
 */
status_t sideload_update_test(void) {
  // Sideload the first key and encrypt the plaintext.
  uint32_t ciphertext1[ARRAYSIZE(kAesPlaintextBlock)];
  TRY(encrypt(kKeySalt1, ciphertext1));

  // Sideload the second key and encrypt the plaintext.
  uint32_t ciphertext2[ARRAYSIZE(kAesPlaintextBlock)];
  TRY(encrypt(kKeySalt2, ciphertext2));

  // Check that the ciphertexts are different.
  TRY_CHECK_ARRAYS_NE(ciphertext1, ciphertext2, ARRAYSIZE(ciphertext1));

  // Sideload the first key again and encrypt the plaintext.
  uint32_t ciphertext3[ARRAYSIZE(kAesPlaintextBlock)];
  TRY(encrypt(kKeySalt1, ciphertext3));

  // Check that the ciphertexts are the same.
  TRY_CHECK_ARRAYS_EQ(ciphertext1, ciphertext3, ARRAYSIZE(ciphertext1));

  return OK_STATUS();
}

/**
 * Test that sideloaded AES keys are properly cleared.
 *
 * Clearing a key should result in an invalid key error.
 */
status_t sideload_clear_test(void) {
  // Sideload the first key and encrypt the plaintext.
  uint32_t ciphertext1[ARRAYSIZE(kAesPlaintextBlock)];
  TRY(encrypt(kKeySalt1, ciphertext1));

  // Construct a mock key for the AES driver.
  uint32_t share0[256 / 32] = {0};
  uint32_t share1[256 / 32] = {0};
  aes_key_t key = {
      .mode = kAesCipherModeCtr,
      .sideload = kHardenedBoolTrue,
      .key_len = kAesKeyConfig.key_length,
      .key_shares = {share0, share1},
  };

  // Construct the IV.
  aes_block_t iv;
  memcpy(iv.data, kAesIv, sizeof(kAesIv));

  // Try to start another encryption operation using the AES driver directly,
  // and expect an error because the sideloaded key is not present.
  TRY_CHECK(!status_ok(aes_encrypt_begin(key, &iv)));

  return OK_STATUS();
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  static status_t result;

  CHECK_STATUS_OK(test_setup());
  EXECUTE_TEST(result, basic_encrypt_decrypt_test);
  EXECUTE_TEST(result, sideload_update_test);
  EXECUTE_TEST(result, sideload_clear_test);

  return status_ok(result);
}
