// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/impl/keyblob.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc_p256.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

enum {
  /* Number of 32-bit words in a P-256 public key. */
  kP256PublicKeyWords = 512 / 32,
  /* Number of 32-bit words in a P-256 signature. */
  kP256SignatureWords = 512 / 32,
  /* Number of 32-bit words in a P-256 signature. */
  kP256DigestWords = 256 / 32,
  /* Number of bytes in a P-256 private key. */
  kP256PrivateKeyBytes = 256 / 8,
  /* Number of bytes in a P-256 secret scalar. */
  kP256SecretScalarBytes = 320 / 8,
  /* Number of words in a P-256 secret scalar. */
  kP256SecretScalarWords = kP256SecretScalarBytes / 4,
  /* Number of bytes in a P-256 scalar input. */
  kP256TestVectorScalarInpBytes = 256 / 8,
  /* Number of words in a P-256 scalar input. */
  kP256TestVectorScalarInpWords = kP256TestVectorScalarInpBytes / 4,
};

// Message
static const char kMessage[] = "test message";

// The KAT vectors are from:
// https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/P256_SHA256.pdf

// Known answer test message.
static const char kKATMessage[] = "Example of ECDSA with P-256";

// Known answer test secret scalar k.
static const uint32_t kKATSecretScalar[kP256TestVectorScalarInpWords] = {
    0xFAEE50AE, 0x14DBB427, 0x04FBE19F, 0x58504BF2,
    0x4DACE391, 0xAA435D2A, 0x797FC8CA, 0x7A1A7E52,
};

// Known answer test key d.
static const uint32_t kKATKey[kP256TestVectorScalarInpWords] = {
    0x4985BF96, 0x04E479C3, 0xA508A1ED, 0x2336F851,
    0xB2D1D812, 0x0657FAA5, 0x5C22CCE2, 0xC477F9F6,
};

// Known answer test expected signature.
static const uint32_t kKATExpSignature[kP256SignatureWords] = {
    0xCA46104F, 0x7325B69A, 0x1F0B3EF5, 0xE44C316F, 0xB1500F81, 0xFF65D1F3,
    0xD07F4165, 0x2B42F576, 0x6B63FAF1, 0x4B329BDB, 0xE69D262C, 0x98C1886F,
    0x89502A81, 0x3E3A993A, 0x2D6392CD, 0xDC42C212,
};

static const otcrypto_key_config_t kPrivateKeyConfig = {
    .version = kOtcryptoLibVersion1,
    .key_mode = kOtcryptoKeyModeEcdsaP256,
    .key_length = kP256PrivateKeyBytes,
    .hw_backed = kHardenedBoolFalse,
    .security_level = kOtcryptoKeySecurityLevelLow,
};

static status_t sign_then_verify_test(void) {
  hardened_bool_t verificationResult;

  // Allocate space for a masked private key.
  uint32_t keyblob[keyblob_num_words(kPrivateKeyConfig)];
  otcrypto_blinded_key_t private_key = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };

  // Allocate space for a public key.
  uint32_t pk[kP256PublicKeyWords] = {0};
  otcrypto_unblinded_key_t public_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = sizeof(pk),
      .key = pk,
  };

  // Generate a keypair.
  LOG_INFO("Generating keypair...");
  CHECK_STATUS_OK(otcrypto_ecdsa_p256_keygen(&private_key, &public_key));

  // Hash the message.
  otcrypto_const_byte_buf_t msg = {
      .len = sizeof(kMessage) - 1,
      .data = (unsigned char *)&kMessage,
  };
  uint32_t msg_digest_data[kP256DigestWords];
  otcrypto_hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
  };
  TRY(otcrypto_sha2_256(msg, &msg_digest));

  // Allocate space for the signature.
  uint32_t sig[kP256SignatureWords] = {0};

  // Generate a signature for the message.
  LOG_INFO("Signing...");
  CHECK_STATUS_OK(otcrypto_ecdsa_p256_sign_verify(
      &private_key, &public_key, msg_digest,
      (otcrypto_word32_buf_t){.data = sig, .len = ARRAYSIZE(sig)}));

  // Verify the signature.
  LOG_INFO("Verifying...");
  CHECK_STATUS_OK(otcrypto_ecdsa_p256_verify(
      &public_key, msg_digest,
      (otcrypto_const_word32_buf_t){.data = sig, .len = ARRAYSIZE(sig)},
      &verificationResult));
  TRY_CHECK(verificationResult == kHardenedBoolTrue);

  return OK_STATUS();
}

static status_t sign_kat(void) {
  // Allocate space for a masked secret scalar.
  uint32_t keyblob_scalar[keyblob_num_words(kPrivateKeyConfig)];
  otcrypto_blinded_key_t secret_scalar = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(keyblob_scalar),
      .keyblob = keyblob_scalar,
  };
  memset(keyblob_scalar, 0, 2 * kP256SecretScalarBytes);
  memcpy(keyblob_scalar, kKATSecretScalar, kP256TestVectorScalarInpBytes);
  secret_scalar.checksum = integrity_blinded_checksum(&secret_scalar);

  // Allocate space for a masked private key.
  uint32_t keyblob_sk[keyblob_num_words(kPrivateKeyConfig)];
  otcrypto_blinded_key_t private_key = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(keyblob_sk),
      .keyblob = keyblob_sk,
  };
  memset(keyblob_sk, 0, 2 * kP256SecretScalarBytes);
  memcpy(keyblob_sk, kKATKey, kP256TestVectorScalarInpBytes);
  private_key.checksum = integrity_blinded_checksum(&private_key);

  // Hash the message.
  otcrypto_const_byte_buf_t msg = {
      .len = sizeof(kKATMessage) - 1,
      .data = (unsigned char *)&kKATMessage,
  };
  uint32_t msg_digest_data[kP256DigestWords];
  otcrypto_hash_digest_t msg_digest = {
      .data = msg_digest_data,
      .len = ARRAYSIZE(msg_digest_data),
  };
  TRY(otcrypto_sha2_256(msg, &msg_digest));

  // Allocate space for the signature.
  uint32_t sig[kP256SignatureWords] = {0};

  // Generate a signature for the message.
  LOG_INFO("Signing...");
  CHECK_STATUS_OK(otcrypto_ecdsa_p256_sign_config_k(
      &private_key, &secret_scalar, msg_digest,
      (otcrypto_word32_buf_t){.data = sig, .len = ARRAYSIZE(sig)}));

  // Check if the signature matches the expected value.
  TRY_CHECK_ARRAYS_EQ(sig, kKATExpSignature, kP256SignatureWords);

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();

  // Initialize the entropy complex.
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());
  EXECUTE_TEST(result, sign_then_verify_test);
  EXECUTE_TEST(result, sign_kat);

  return status_ok(result);
}
