// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc_curve25519.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

enum {
  /* Number of bytes needed to store the private key. */
  kEd25519PrivateKeyBytes = 32,
  /* Number of words needed to store the private key. */
  kEd25519PrivateKeyWords = kEd25519PrivateKeyBytes / sizeof(uint32_t),
  /* Number of bytes needed to store the signature. */
  kEd25519SignatureBytes = 64,
  /* Number of words needed to store the signature. */
  kEd25519SignatureWords = kEd25519SignatureBytes / sizeof(uint32_t),
  /* Number of bytes needed to store the public key. */
  kEd25519PublicKeyBytes = 32,
  /* Number of words needed to store the public key. */
  kEd25519PublicKeyWords = kEd25519PublicKeyBytes / sizeof(uint32_t),
  /* Length of a masked secret scalar share in bytes.
   * This implementation uses extra redundant bits for side-channel protection.
   */
  kEd25519MaskedScalarShareBytes = kEd25519PrivateKeyBytes + 8,
  /* Length of masked secret scalar share in words. */
  kEd25519MaskedScalarShareWords =
      kEd25519MaskedScalarShareBytes / sizeof(uint32_t),
  /* Number of shares for the scalar. */
  kEd25519MaskedScalarNumShares = 2,
  /* Length of the full masked secret scalar share in bytes. */
  kEd25519MaskedScalarTotalShareBytes =
      kEd25519MaskedScalarNumShares * kEd25519MaskedScalarShareBytes,
  /* Length of the full masked secret scalar share in words. */
  kEd25519MaskedScalarTotalShareWords =
      kEd25519MaskedScalarNumShares * kEd25519MaskedScalarShareWords,
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
static uint32_t kSecretKey[] = {0x9b08cd4c, 0xda96ff28, 0x46c3b69d, 0x0f4e11ec,
                                0x9f318a5b, 0x24a6ab35, 0xedf68cda, 0xfba6b84f,
                                0x00000000, 0x00000000};

// SECRET KEY SHARE 0 (Pre-computed such that Share0 - Share1 = Secret Key)
// static uint32_t kSecretKeyShare0[] = {
//     0xac19de5d, 0xeba81039, 0x57d4c7ae, 0x105f22fd,
//     0xb0429b6c, 0x35b7bc46, 0xfe079deb, 0x0cb7c960,
// };

// SECRET KEY SHARE 1 (Pre-computed fixed share)
static uint32_t kSecretKeyShare1[] = {
    0x11111111, 0x11111111, 0x11111111, 0x01111111, 0x11111111,
    0x11111111, 0x11111111, 0x11111111, 0x00000000, 0x00000000};

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

status_t ed25519_kat_test(void) {
  LOG_INFO("Running Ed25519 KAT Test");

  // Set up private_key struct (blinded).
  uint32_t keyblob[keyblob_num_words(kPrivateKeyConfig)];
  memset(keyblob, 0, sizeof(keyblob));

  size_t share_words = keyblob_share_num_words(kPrivateKeyConfig);

  uint32_t kSecretKeyShare0[kEd25519MaskedScalarShareWords] = {0};
  TRY(hardened_add(kSecretKey, kSecretKeyShare1, kEd25519MaskedScalarShareWords,
                   kSecretKeyShare0));
  memcpy(keyblob, kSecretKeyShare0, kEd25519MaskedScalarShareBytes);
  memcpy(keyblob + share_words, kSecretKeyShare1,
         kEd25519MaskedScalarShareBytes);

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
  CHECK_STATUS_OK(otcrypto_ed25519_keygen(&private_key, &public_key));
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
  memset(keyblob, 0, sizeof(keyblob));
  uint32_t kSecretKeyShare0[kEd25519MaskedScalarShareWords] = {0};
  TRY(hardened_add(kSecretKey, kSecretKeyShare1, kEd25519MaskedScalarShareWords,
                   kSecretKeyShare0));
  size_t share_words = keyblob_share_num_words(kPrivateKeyConfig);
  memcpy(keyblob, kSecretKeyShare0, kEd25519MaskedScalarShareBytes);
  memcpy(keyblob + share_words, kSecretKeyShare1,
         kEd25519MaskedScalarShareBytes);

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

  CHECK_STATUS_OK(otcrypto_ed25519_keygen(&private_key, &public_key));

  otcrypto_const_byte_buf_t input_message = {
      .data = (const uint8_t *)kMessage,
      .len = ARRAYSIZE(kMessage),
  };

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
 * Execute negative testing.
 */
static status_t run_negative_tests(void) {
  LOG_INFO("Running negative tests");

  uint32_t priv_keyblob[keyblob_num_words(kPrivateKeyConfig)];
  memset(priv_keyblob, 0, sizeof(priv_keyblob));

  size_t share_words = keyblob_share_num_words(kPrivateKeyConfig);
  uint32_t kSecretKeyShare0[kEd25519MaskedScalarShareWords] = {0};
  TRY(hardened_add(kSecretKey, kSecretKeyShare1, kEd25519MaskedScalarShareWords,
                   kSecretKeyShare0));
  memcpy(priv_keyblob, kSecretKeyShare0, kEd25519PrivateKeyBytes);
  memcpy(priv_keyblob + share_words, kSecretKeyShare1, kEd25519PrivateKeyBytes);

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
  otcrypto_blinded_key_t bad_len_key = {
      .config = bad_len_cfg,
      .keyblob_length = sizeof(priv_keyblob),
      .keyblob = priv_keyblob,
  };
  bad_len_key.checksum = integrity_blinded_checksum(&bad_len_key);
  CHECK(otcrypto_ed25519_keygen(&bad_len_key, &valid_pub).value ==
        OTCRYPTO_BAD_ARGS.value);

  // Test with invalid mode
  otcrypto_key_config_t bad_mode_cfg = kPrivateKeyConfig;
  bad_mode_cfg.key_mode = kOtcryptoKeyModeEcdsaP256;
  otcrypto_blinded_key_t bad_mode_key = {
      .config = bad_mode_cfg,
      .keyblob_length = sizeof(priv_keyblob),
      .keyblob = priv_keyblob,
  };
  bad_mode_key.checksum = integrity_blinded_checksum(&bad_mode_key);
  CHECK(otcrypto_ed25519_keygen(&bad_mode_key, &valid_pub).value ==
        OTCRYPTO_BAD_ARGS.value);

  // Test with NULL keyblob
  otcrypto_blinded_key_t bad_keyblob_key = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(priv_keyblob),
      .keyblob = NULL,
  };
  // Note: we don't compute the checksum here because the keyblob pointer is
  // NULL
  CHECK(otcrypto_ed25519_keygen(&bad_keyblob_key, &valid_pub).value ==
        OTCRYPTO_BAD_ARGS.value);

  // Test with corrupted checksum
  otcrypto_blinded_key_t bad_chk_key = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(priv_keyblob),
      .keyblob = priv_keyblob,
  };
  bad_chk_key.checksum = valid_priv.checksum ^ 0xFFFFFFFF;
  CHECK(otcrypto_ed25519_keygen(&bad_chk_key, &valid_pub).value ==
        OTCRYPTO_BAD_ARGS.value);

  // Test with NULL private key pointer
  CHECK(otcrypto_ed25519_keygen(NULL, &valid_pub).value ==
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

  CHECK_STATUS_OK(entropy_complex_init());

  EXECUTE_TEST(result, ed25519_kat_test);
  EXECUTE_TEST(result, hasheddsa_test);
  EXECUTE_TEST(result, run_negative_tests);

  return status_ok(result);
}
