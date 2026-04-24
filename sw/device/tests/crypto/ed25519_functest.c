// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc_curve25519.h"
#include "sw/device/lib/crypto/include/entropy_src.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

enum {
  /* Number of bytes needed to store the private key. */
  kEd25519PrivateKeyBytes = 32,
  /* Number of words needed to store the private key. */
  kEd25519PrivateKeyWords = kEd25519PrivateKeyBytes / 4,
  /* Number of bytes needed to store the private key. */
  kEd25519SignatureBytes = 64,
  /* Number of words needed to store the private key. */
  kEd25519SignatureWords = kEd25519SignatureBytes / 4,
  /* Number of bytes needed to store the public key. */
  kEd25519PublicKeyBytes = 32,
  /* Number of words needed to store the public key. */
  kEd25519PublicKeyWords = kEd25519PublicKeyBytes / 4,
};

// This test vector stems from RFC 8032 section 7.1 TEST 2:
// https://datatracker.ietf.org/doc/html/rfc8032#section-7.1

//  ALGORITHM:
//  Ed25519

//  SECRET KEY:
//  4ccd089b28ff96da9db6c346ec114e0f
//  5b8a319f35aba624da8cf6ed4fb8a6fb

//  PUBLIC KEY:
//  3d4017c3e843895a92b70aa74d1b7ebc
//  9c982ccf2ec4968cc0cd55f12af4660c

//  MESSAGE (length 1 byte):
//  72

//  SIGNATURE:
//  92a009a9f0d4cab8720e820b5f642540
//  a2b27b5416503f8fb3762223ebdb69da
//  085ac1e43e15996e458f3613d0f11d8c
//  387b2eaeb4302aeeb00d291612bb0c00

//  SECRET KEY (WORD & BYTE SWAPPED)
static uint32_t kSecretKey[] = {
    0x9b08cd4c, 0xda96ff28, 0x46c3b69d, 0x0f4e11ec,
    0x9f318a5b, 0x24a6ab35, 0xedf68cda, 0xfba6b84f,
};

//  Public KEY (WORD & BYTE SWAPPED)
static uint32_t kPublicKey[] = {
    0xc317403d, 0x5a8943e8, 0xa70ab792, 0xbc7e1b4d,
    0xcf2c989c, 0x8c96c42e, 0xf155cdc0, 0x0c66f42a,
};

//  Signature
//  R: (WORD SWAPPED)
//  S: (WORD & BYTE SWAPPED)
static uint32_t kSignature[] = {
    // R
    0xebdb69da,
    0xb3762223,
    0x16503f8f,
    0xa2b27b54,
    0x5f642540,
    0x720e820b,
    0xf0d4cab8,
    0x92a009a9,
    // S
    0xe4c15a08,
    0x6e99153e,
    0x13368f45,
    0x8c1df1d0,
    0xae2e7b38,
    0xee2a30b4,
    0x16290db0,
    0x000cbb12,
};

// MESSAGE (length 1 byte):
static const char kMessage[] = {
    0x72,
};

static const otcrypto_key_config_t kPrivateKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeEd25519,
    .key_length = kEd25519PrivateKeyBytes,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

/**
 * Helper function to securely populate the keyblob array with two shares.
 */
static status_t create_blinded_kat_keyblob(uint32_t *keyblob) {
  // Zero out the entire blob to avoid checksumming uninitialized padding
  memset(keyblob, 0, keyblob_num_words(kPrivateKeyConfig) * sizeof(uint32_t));

  uint32_t *share0 = keyblob;
  uint32_t *share1 = keyblob + keyblob_share_num_words(kPrivateKeyConfig);

  // Generate a random mask for share1 (only need 8 words for the seed)
  HARDENED_TRY(hardened_memshred(share1, kEd25519PrivateKeyWords));

  // Calculate share0 = kSecretKey - share1 (implicitly modulo 2^256)
  HARDENED_TRY(
      hardened_sub(kSecretKey, share1, kEd25519PrivateKeyWords, share0));

  return OTCRYPTO_OK;
}

status_t ed25519_kat_test(void) {
  LOG_INFO("Running Ed25519 KAT Test");

  uint32_t keyblob[keyblob_num_words(kPrivateKeyConfig)];
  CHECK_STATUS_OK(create_blinded_kat_keyblob(keyblob));

  otcrypto_blinded_key_t private_key = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  private_key.checksum = integrity_blinded_checksum(&private_key);

  // Set up public_key struct.
  uint32_t public_key_buf[kEd25519PublicKeyWords];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEd25519,
      .key_length = kEd25519PublicKeyBytes,
      .key = public_key_buf,
  };

  // Run ed25519 key generation.
  CHECK_STATUS_OK(
      otcrypto_ed25519_public_key_from_private(&private_key, &public_key));
  // Check the ed25519 key generation result.
  TRY_CHECK_ARRAYS_EQ(kPublicKey, public_key.key, kEd25519PublicKeyWords);

  // Set up input_message struct.
  otcrypto_const_byte_buf_t input_message =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, (const uint8_t *)kMessage,
                        ARRAYSIZE(kMessage));
  // Set up signature struct.
  uint32_t signature_data[kEd25519SignatureWords];
  otcrypto_word32_buf_t signature = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, signature_data, ARRAYSIZE(signature_data));

  // Run ed25519 signature generation.
  CHECK_STATUS_OK(otcrypto_ed25519_sign(
      &private_key, &input_message, kOtcryptoEddsaSignModeEddsa, &signature));
  // Check the ed25519 signature generation result.
  TRY_CHECK_ARRAYS_EQ(kSignature, signature.data, kEd25519SignatureWords);

  // Set up signature struct for verification.
  const uint32_t *const signature_verif_data =
      (const uint32_t *const)signature_data;
  otcrypto_const_word32_buf_t signature_verif =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, signature_verif_data,
                        ARRAYSIZE(signature_data));

  // Run ed25519 signature verification.
  hardened_bool_t verification_result;
  CHECK_STATUS_OK(otcrypto_ed25519_verify(
      &public_key, &input_message, kOtcryptoEddsaSignModeEddsa,
      &signature_verif, &verification_result));

  // Signature verification is expected to succeed.
  TRY_CHECK(verification_result == kHardenedBoolTrue);

  return OTCRYPTO_OK;
}

/**
 * Run a sign and verify loop utilizing the HashEdDSA sign mode
 */
static status_t hasheddsa_test(void) {
  LOG_INFO("Running HashEdDSA test");

  uint32_t keyblob[keyblob_num_words(kPrivateKeyConfig)];
  CHECK_STATUS_OK(create_blinded_kat_keyblob(keyblob));

  otcrypto_blinded_key_t private_key = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  private_key.checksum = integrity_blinded_checksum(&private_key);

  uint32_t public_key_buf[kEd25519PublicKeyWords];
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEd25519,
      .key_length = kEd25519PublicKeyBytes,
      .key = public_key_buf,
  };

  CHECK_STATUS_OK(
      otcrypto_ed25519_public_key_from_private(&private_key, &public_key));

  otcrypto_const_byte_buf_t input_message =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, (const uint8_t *)kMessage,
                        ARRAYSIZE(kMessage));

  uint32_t signature_data[kEd25519SignatureWords];
  otcrypto_word32_buf_t signature = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, signature_data, ARRAYSIZE(signature_data));

  CHECK_STATUS_OK(otcrypto_ed25519_sign(&private_key, &input_message,
                                        kOtcryptoEddsaSignModeHashEddsa,
                                        &signature));

  const uint32_t *const signature_verif_data =
      (const uint32_t *const)signature_data;
  otcrypto_const_word32_buf_t signature_verif =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, signature_verif_data,
                        ARRAYSIZE(signature_data));

  hardened_bool_t verification_result;
  CHECK_STATUS_OK(otcrypto_ed25519_verify(
      &public_key, &input_message, kOtcryptoEddsaSignModeHashEddsa,
      &signature_verif, &verification_result));

  TRY_CHECK(verification_result == kHardenedBoolTrue);

  return OTCRYPTO_OK;
}

/**
 * Test the combined sign-and-verify function.
 */
static status_t sign_verify_test(void) {
  LOG_INFO("Running sign_verify test");

  uint32_t keyblob[keyblob_num_words(kPrivateKeyConfig)];
  CHECK_STATUS_OK(create_blinded_kat_keyblob(keyblob));

  otcrypto_blinded_key_t private_key = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  private_key.checksum = integrity_blinded_checksum(&private_key);

  // Set up public_key struct.
  uint32_t public_key_buf[kEd25519PublicKeyWords];
  memcpy(public_key_buf, kPublicKey, kEd25519PublicKeyBytes);
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEd25519,
      .key_length = kEd25519PublicKeyBytes,
      .key = public_key_buf,
  };
  public_key.checksum = integrity_unblinded_checksum(&public_key);

  // Set up input_message struct.
  otcrypto_const_byte_buf_t input_message =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, (const uint8_t *)kMessage,
                        ARRAYSIZE(kMessage));

  // Set up signature struct.
  uint32_t signature_data[kEd25519SignatureWords];
  otcrypto_word32_buf_t signature = OTCRYPTO_MAKE_BUF(
      otcrypto_word32_buf_t, signature_data, ARRAYSIZE(signature_data));

  // Run combined ed25519 signature generation and verification.
  CHECK_STATUS_OK(
      otcrypto_ed25519_sign_verify(&private_key, &public_key, &input_message,
                                   kOtcryptoEddsaSignModeEddsa, &signature));

  // Check the ed25519 signature generation result still matches the KAT.
  TRY_CHECK_ARRAYS_EQ(kSignature, signature.data, kEd25519SignatureWords);

  return OTCRYPTO_OK;
}

/**
 * Execute negative testing.
 */
static status_t run_negative_tests(void) {
  LOG_INFO("Running negative tests");

  uint32_t priv_keyblob[keyblob_num_words(kPrivateKeyConfig)];
  CHECK_STATUS_OK(create_blinded_kat_keyblob(priv_keyblob));

  otcrypto_blinded_key_t valid_priv = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(priv_keyblob),
      .keyblob = priv_keyblob,
  };
  valid_priv.checksum = integrity_blinded_checksum(&valid_priv);

  uint32_t public_key_buf[kEd25519PublicKeyWords];
  otcrypto_unblinded_key_t valid_pub = {
      .key_mode = kOtcryptoKeyModeEd25519,
      .key_length = kEd25519PublicKeyBytes,
      .key = public_key_buf,
  };
  valid_pub.checksum = integrity_unblinded_checksum(&valid_pub);

  otcrypto_const_byte_buf_t msg =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, (const uint8_t *)kMessage,
                        ARRAYSIZE(kMessage));

  otcrypto_const_byte_buf_t bad_msg =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, NULL, 5);

  uint32_t sig_buf[kEd25519SignatureWords];
  otcrypto_word32_buf_t sig =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig_buf, kEd25519SignatureWords);

  // Test ed25519_key_check with invalid key length
  otcrypto_key_config_t bad_len_cfg = kPrivateKeyConfig;
  bad_len_cfg.key_length = 31;
  otcrypto_blinded_key_t bad_key_len = {
      .config = bad_len_cfg,
      .keyblob_length = sizeof(priv_keyblob),
      .keyblob = priv_keyblob,
  };
  bad_key_len.checksum = integrity_blinded_checksum(&bad_key_len);
  CHECK(otcrypto_ed25519_public_key_from_private(&bad_key_len, &valid_pub)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Test ed25519_key_check with invalid key mode
  otcrypto_key_config_t bad_mode_cfg = kPrivateKeyConfig;
  bad_mode_cfg.key_mode = kOtcryptoKeyModeEcdsaP256;
  otcrypto_blinded_key_t bad_key_mode = {
      .config = bad_mode_cfg,
      .keyblob_length = sizeof(priv_keyblob),
      .keyblob = priv_keyblob,
  };
  bad_key_mode.checksum = integrity_blinded_checksum(&bad_key_mode);
  CHECK(otcrypto_ed25519_public_key_from_private(&bad_key_mode, &valid_pub)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Test ed25519_key_check with NULL data
  otcrypto_blinded_key_t bad_key_null = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(priv_keyblob),
      .keyblob = NULL,
  };
  CHECK(otcrypto_ed25519_public_key_from_private(&bad_key_null, &valid_pub)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Test ed25519_key_check with bad checksum
  otcrypto_blinded_key_t bad_key_chk = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(priv_keyblob),
      .keyblob = priv_keyblob,
  };
  bad_key_chk.checksum = valid_priv.checksum ^ 0xFFFFFFFF;
  CHECK(otcrypto_ed25519_public_key_from_private(&bad_key_chk, &valid_pub)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Null pointer tests
  CHECK(otcrypto_ed25519_public_key_from_private(NULL, &valid_pub).value ==
        OTCRYPTO_BAD_ARGS.value);

  // Test NULL data with len > 0 or invalid mode
  CHECK(otcrypto_ed25519_sign(&valid_priv, &bad_msg,
                              kOtcryptoEddsaSignModeEddsa, &sig)
            .value == OTCRYPTO_BAD_ARGS.value);

  CHECK(otcrypto_ed25519_sign(&valid_priv, &msg,
                              (otcrypto_eddsa_sign_mode_t)0xFF, &sig)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Test NULL pointer, bad length, or NULL data
  otcrypto_word32_buf_t bad_sig =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig_buf, 15);
  CHECK(otcrypto_ed25519_sign(&valid_priv, &msg, kOtcryptoEddsaSignModeEddsa,
                              &bad_sig)
            .value == OTCRYPTO_BAD_ARGS.value);

  bad_sig.data = NULL;
  bad_sig.len = kEd25519SignatureWords;
  CHECK(otcrypto_ed25519_sign(&valid_priv, &msg, kOtcryptoEddsaSignModeEddsa,
                              &bad_sig)
            .value == OTCRYPTO_BAD_ARGS.value);

  CHECK(otcrypto_ed25519_sign(&valid_priv, &msg, kOtcryptoEddsaSignModeEddsa,
                              NULL)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Bad signature verification
  otcrypto_const_word32_buf_t bad_const_sig =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, sig_buf, 15);
  hardened_bool_t verify_res;
  CHECK(otcrypto_ed25519_verify(&valid_pub, &msg, kOtcryptoEddsaSignModeEddsa,
                                &bad_const_sig, &verify_res)
            .value == OTCRYPTO_BAD_ARGS.value);

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();

  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  EXECUTE_TEST(result, ed25519_kat_test);
  EXECUTE_TEST(result, hasheddsa_test);
  EXECUTE_TEST(result, sign_verify_test);
  EXECUTE_TEST(result, run_negative_tests);

  return status_ok(result);
}
