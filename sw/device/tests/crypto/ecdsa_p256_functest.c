// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/impl/integrity.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc_p256.h"
#include "sw/device/lib/crypto/include/keyblob.h"
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
  uint32_t keyblob_len = 2 * kP256SecretScalarWords;

  // Allocate space for a masked secret scalar.
  uint32_t keyblob_scalar[keyblob_len];
  otcrypto_blinded_key_t secret_scalar = {
      .config = kPrivateKeyConfig,
      .keyblob_length = sizeof(keyblob_scalar),
      .keyblob = keyblob_scalar,
  };
  memset(keyblob_scalar, 0, 2 * kP256SecretScalarBytes);
  memcpy(keyblob_scalar, kKATSecretScalar, kP256TestVectorScalarInpBytes);
  secret_scalar.checksum = integrity_blinded_checksum(&secret_scalar);

  // Allocate space for a masked private key.
  uint32_t keyblob_sk[keyblob_len];
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

static status_t run_ecdsa_negative_tests(void) {
  LOG_INFO("Running ECDSA negative tests.");

  uint32_t priv_keyblob[80 / 4] = {0};
  otcrypto_blinded_key_t valid_priv = {
      .config = kPrivateKeyConfig,
      .keyblob_length = 80,
      .keyblob = priv_keyblob,
  };
  valid_priv.checksum = integrity_blinded_checksum(&valid_priv);

  uint32_t pub_key_data[64 / 4] = {0};
  otcrypto_unblinded_key_t valid_pub = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = 64,
      .key = pub_key_data,
  };
  valid_pub.checksum = integrity_unblinded_checksum(&valid_pub);

  uint32_t digest_data[32 / 4] = {0};
  otcrypto_hash_digest_t valid_digest = {
      .data = digest_data,
      .len = 8,
  };

  uint32_t sig_data[64 / 4] = {0};
  otcrypto_word32_buf_t valid_sig = {
      .data = sig_data,
      .len = 16,
  };
  otcrypto_const_word32_buf_t valid_const_sig = {
      .data = sig_data,
      .len = 16,
  };
  hardened_bool_t verify_res;

  // ECDSA keygen negative tests
  CHECK(otcrypto_ecdsa_p256_keygen(NULL, &valid_pub).value ==
        OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_ecdsa_p256_keygen(&valid_priv, NULL).value ==
        OTCRYPTO_BAD_ARGS.value);

  // Null pointer keyblob
  otcrypto_blinded_key_t bad_priv_null = {
      .config = kPrivateKeyConfig,
      .keyblob_length = 80,
      .keyblob = NULL,
  };
  CHECK(otcrypto_ecdsa_p256_keygen(&bad_priv_null, &valid_pub).value ==
        OTCRYPTO_BAD_ARGS.value);

  // Bad mode
  otcrypto_key_config_t bad_mode_cfg = kPrivateKeyConfig;
  bad_mode_cfg.key_mode = kOtcryptoKeyModeEcdhP256;
  otcrypto_blinded_key_t bad_priv_mode = {
      .config = bad_mode_cfg,
      .keyblob_length = 80,
      .keyblob = priv_keyblob,
  };
  bad_priv_mode.checksum = integrity_blinded_checksum(&bad_priv_mode);
  CHECK(otcrypto_ecdsa_p256_keygen(&bad_priv_mode, &valid_pub).value ==
        OTCRYPTO_BAD_ARGS.value);

  // Bad public key length
  otcrypto_unblinded_key_t bad_pub_len = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = 63,
      .key = pub_key_data,
  };
  bad_pub_len.checksum = integrity_unblinded_checksum(&bad_pub_len);
  CHECK(otcrypto_ecdsa_p256_keygen(&valid_priv, &bad_pub_len).value ==
        OTCRYPTO_BAD_ARGS.value);

  // ECDSA sign negative tests
  CHECK(otcrypto_ecdsa_p256_sign(NULL, valid_digest, valid_sig).value ==
        OTCRYPTO_BAD_ARGS.value);

  // Null digest data
  otcrypto_hash_digest_t bad_digest_null = {
      .data = NULL,
      .len = 8,
  };
  CHECK(
      otcrypto_ecdsa_p256_sign(&valid_priv, bad_digest_null, valid_sig).value ==
      OTCRYPTO_BAD_ARGS.value);

  // Bad digest length
  otcrypto_hash_digest_t bad_digest_len = {
      .data = digest_data,
      .len = 7,
  };
  CHECK(
      otcrypto_ecdsa_p256_sign(&valid_priv, bad_digest_len, valid_sig).value ==
      OTCRYPTO_BAD_ARGS.value);

  // Null signature data
  otcrypto_word32_buf_t bad_sig_null = {
      .data = NULL,
      .len = 16,
  };
  CHECK(
      otcrypto_ecdsa_p256_sign(&valid_priv, valid_digest, bad_sig_null).value ==
      OTCRYPTO_BAD_ARGS.value);

  // Corrupt private key checksum
  otcrypto_blinded_key_t bad_priv_chk = {
      .config = kPrivateKeyConfig,
      .keyblob_length = 80,
      .keyblob = priv_keyblob,
  };
  bad_priv_chk.checksum = valid_priv.checksum ^ 0xFFFFFFFF;
  CHECK(
      otcrypto_ecdsa_p256_sign(&bad_priv_chk, valid_digest, valid_sig).value ==
      OTCRYPTO_BAD_ARGS.value);

  // ECDSA verify negative tests
  CHECK(otcrypto_ecdsa_p256_verify(NULL, valid_digest, valid_const_sig,
                                   &verify_res)
            .value == OTCRYPTO_BAD_ARGS.value);
  CHECK(otcrypto_ecdsa_p256_verify(&valid_pub, valid_digest, valid_const_sig,
                                   NULL)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Corrupt public key checksum
  otcrypto_unblinded_key_t bad_pub_chk = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = 64,
      .key = pub_key_data,
  };
  bad_pub_chk.checksum = valid_pub.checksum ^ 0xFFFFFFFF;
  CHECK(otcrypto_ecdsa_p256_verify(&bad_pub_chk, valid_digest, valid_const_sig,
                                   &verify_res)
            .value == OTCRYPTO_BAD_ARGS.value);

  // Bad signature length
  otcrypto_const_word32_buf_t bad_const_sig_len = {
      .data = sig_data,
      .len = 15,
  };
  CHECK(otcrypto_ecdsa_p256_verify(&valid_pub, valid_digest, bad_const_sig_len,
                                   &verify_res)
            .value == OTCRYPTO_BAD_ARGS.value);

  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  status_t result = OK_STATUS();

  // Initialize the entropy complex.
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());
  EXECUTE_TEST(result, sign_then_verify_test);
  EXECUTE_TEST(result, sign_kat);
  EXECUTE_TEST(result, run_ecdsa_negative_tests);

  return status_ok(result);
}
